"""Release/tag acquisition and subprocess isolation for external ATP benchmarks.

Only Python's standard library is used. Downloaded projects and the private opam
root live in a directory created by mktemp, never in the source repository.
"""
import configparser
import contextlib
import gzip
import hashlib
import json
import math
import os
import pathlib
import platform
import re
import shlex
import shutil
import signal
import subprocess
import tarfile
import tempfile
import threading
import time
import urllib.parse
import zipfile
from dataclasses import dataclass

REPOSITORIES = {
    "eprover": "eprover/eprover",
    "vampire": "vprover/vampire",
    "zipperposition": "sneeuwballen/zipperposition",
}

# The Release 2.1 opam files predate these compatibility bounds, which were
# subsequently added to opam-repository's logtk.2.1 / zipperposition.2.1 metadata.
# Apply them only to that source commit; keep the downloaded sources unchanged.
ZIPPER_DEPENDENCY_BOUNDS = {
    "1051eaafb0040262f1e9acd338e0f605cd2d8c17": ["mtime<2.0", "menhir<20211215"],
}


class SetupError(RuntimeError):
    pass


class ProcessCleanupError(RuntimeError):
    pass


class _ClockReadError(ProcessCleanupError):
    pass


def sha256(path):
    digest = hashlib.sha256()
    with pathlib.Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def host_target():
    system = platform.system().lower()
    machine = platform.machine().lower()
    machine = {"amd64": "x86_64", "x64": "x86_64", "aarch64": "arm64"}.get(machine, machine)
    if system not in ("darwin", "linux") or machine not in ("arm64", "x86_64"):
        raise SetupError(f"unsupported host: {system}/{machine} (Darwin/Linux, arm64/x86_64 required)")
    return system, machine


def asset_score(name, system, machine):
    """Conservative filename filter; the actual binary header is checked too."""
    name = name.lower()
    if re.search(r"(?:sha\d*|checksum|signature|\.asc$|\.txt$|\.dmg$|\.deb$|\.rpm$|\.msi$)", name):
        return 0
    mac = bool(re.search(r"darwin|macos|mac[-_]?os|osx|apple", name))
    linux = "linux" in name
    if (system == "darwin" and (not mac or linux)) or (system == "linux" and (not linux or mac)):
        return 0
    arm = bool(re.search(r"aarch64|arm64", name))
    x86 = bool(re.search(r"x86[-_]?64|amd64|x64", name))
    universal = system == "darwin" and "universal" in name
    if not universal and ((machine == "arm64" and x86 and not arm)
                          or (machine == "x86_64" and arm and not x86)):
        return 0
    return 3 if universal or (arm if machine == "arm64" else x86) else 1


@dataclass(frozen=True)
class _ClockSample:
    wall_ns: int
    awake_ns: int
    span_ns: int


@dataclass(frozen=True)
class _WallClock:
    clock_id: int
    name: str
    resolution_ns: int
    awake_clock: str
    awake_resolution_ns: int

    def now_ns(self):
        try:
            return time.clock_gettime_ns(self.clock_id)
        except (AttributeError, OSError, ValueError) as error:
            raise _ClockReadError(f"cannot read suspend-aware wall clock {self.name}: {error}") from error

    def info(self):
        return {"wall_clock": self.name, "wall_clock_source": "time.clock_gettime_ns",
                "wall_clock_suspend_aware": True, "awake_clock": self.awake_clock}

    def sample(self, wall_ns=None):
        # Keep the first reading as the timestamp, especially in the reaper.
        # Bracketing the awake reading bounds ordinary preemption between reads;
        # an unbracketed clock difference can falsely look like system suspend.
        wall_ns = self.now_ns() if wall_ns is None else wall_ns
        awake_ns = time.monotonic_ns()
        return _ClockSample(wall_ns, awake_ns, self.now_ns() - wall_ns)


def _wall_clock():
    system = platform.system()
    # Darwin RAW includes suspend; Linux RAW explicitly excludes it.
    name = {"Darwin": "CLOCK_MONOTONIC_RAW", "Linux": "CLOCK_BOOTTIME"}.get(system)
    if name is None:
        raise SetupError(f"no supported suspend-aware wall clock on {system}; Darwin/Linux required")
    try:
        clock_id = getattr(time, name)
        time.clock_gettime_ns(clock_id)  # Fail before spawning if the OS rejects it.
        resolution_ns = max(1, math.ceil(time.clock_getres(clock_id) * 1e9))
        awake = time.get_clock_info("monotonic")
    except (AttributeError, OSError, ValueError) as error:
        raise SetupError(f"suspend-aware wall clock {name} unavailable on {system}: {error}") from error
    return _WallClock(clock_id, name, resolution_ns, awake.implementation,
                      max(1, math.ceil(awake.resolution * 1e9)))


def wall_clock_info():
    """Describe the supported clock before a run; raise SetupError if unavailable."""
    return _wall_clock().info()


def _wait_until(exited, clock, deadline_ns):
    while not exited.is_set():
        remaining = (deadline_ns - clock.now_ns()) / 1e9
        if remaining <= 0:
            return exited.is_set()
        # Event's underlying timeout may exclude system suspend. Recheck the
        # continuous deadline after at most 100ms of awake waiting on resume.
        exited.wait(min(remaining, .1))
    return True


def _cleanup_group(process, exited, clock, output):
    # Kill the group even if its leader already exited: no orphaned search
    # processes may spill into the next timed measurement.
    cleanup_deadline = clock.now_ns() + 1_000_000_000
    while True:
        try:
            os.killpg(process.pid, signal.SIGKILL)
            break
        except ProcessLookupError:
            break
        except PermissionError as error:
            # Darwin can return EPERM for a group containing only zombies.
            # A direct kill never proves that descendants have stopped.
            try:
                process.kill()
            except OSError:
                pass
            if clock.now_ns() >= cleanup_deadline:
                raise ProcessCleanupError(
                    f"cannot stop process group {process.pid}: {error}; "
                    f"benchmark aborted; see {output}") from error
            time.sleep(.01)
        except OSError as error:
            raise ProcessCleanupError(
                f"cannot stop process group {process.pid}: {error}; "
                f"benchmark aborted; see {output}") from error
    if not _wait_until(exited, clock, cleanup_deadline):
        raise ProcessCleanupError(
            f"process {process.pid} did not exit after SIGKILL; "
            f"benchmark aborted; see {output}")


def _cleanup_without_clock(process, output):
    """Emergency cleanup only: no valid measurement or wall deadline fallback."""
    group_error = None
    for attempt in range(100):
        try:
            os.killpg(process.pid, signal.SIGKILL)
            group_error = None
            break
        except ProcessLookupError:
            group_error = None
            break
        except OSError as error:
            group_error = error
            try:
                process.kill()
            except OSError:
                pass
            if not isinstance(error, PermissionError) or attempt == 99:
                break
            time.sleep(.01)
    # Reap even when group signalling failed, or a waiter could not start.
    # Popen.wait serializes concurrent waitpid calls with the existing reaper.
    reaped = False
    for _ in range(10):
        try:
            process.wait(timeout=.1)
            reaped = True
            break
        except subprocess.TimeoutExpired:
            pass
        except OSError:
            break
    if group_error is not None:
        raise ProcessCleanupError(
            f"cannot stop process group {process.pid}: {group_error}; "
            f"benchmark aborted; see {output}") from group_error
    if not reaped:
        raise ProcessCleanupError(
            f"process {process.pid} did not exit after SIGKILL during emergency cleanup; "
            f"benchmark aborted; see {output}")


def run_logged(command, output, seconds, *, cwd=None, env=None, stderr=None):
    """Apply a suspend-inclusive wall deadline to the entire process group.

    Clock observations describe startup through reaping, excluding cleanup.
    A clock gap is evidence to inspect, not a definitive sleep classification.
    Unsupported clocks fail before spawning; there is no awake-only fallback.
    """
    clock = _wall_clock()
    started = clock.sample()
    deadline_ns = started.wall_ns + math.ceil(seconds * 1e9)
    with pathlib.Path(output).open("ab") as stream:
        with contextlib.ExitStack() as stack:
            errors = stack.enter_context(pathlib.Path(stderr).open("ab")) if stderr else subprocess.STDOUT
            wait_errors = []
            finished = finished_sample = None
            waiter_started = False
            process = subprocess.Popen(
                [str(x) for x in command], cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                stdout=stream, stderr=errors, start_new_session=True,
            )
            try:
                exited = threading.Event()
                def reap():
                    nonlocal finished, finished_sample
                    try:
                        try:
                            process.wait()
                        finally:
                            finished = clock.now_ns()
                            finished_sample = clock.sample(finished)
                    except BaseException as error:
                        wait_errors.append(error)
                    finally:
                        exited.set()
                # Record exit immediately in the reaper; all signalling and
                # cleanup errors stay in the caller, even if start() fails.
                waiter = threading.Thread(target=reap, daemon=True)
                waiter.start()
                waiter_started = True
                timed_out = not _wait_until(exited, clock, deadline_ns)
                if finished is not None and finished <= deadline_ns:
                    # The reaper may be preempted between its timestamp and
                    # notification; do not turn an on-time exit into a timeout.
                    timed_out = False
            except Exception as error:
                if not waiter_started:
                    raise ProcessCleanupError(
                        f"cannot start process reaper for {process.pid}: {error}; "
                        f"benchmark aborted; see {output}") from error
                raise
            finally:
                if not waiter_started:
                    _cleanup_without_clock(process, output)
                else:
                    try:
                        _cleanup_group(process, exited, clock, output)
                    except _ClockReadError:
                        _cleanup_without_clock(process, output)
                        raise
            if wait_errors:
                raise ProcessCleanupError(f"cannot reap process {process.pid}: {wait_errors[0]}") from wait_errors[0]
    wall_ns = finished - started.wall_ns
    awake_ns = finished_sample.awake_ns - started.awake_ns
    # Conservatively include timestamp quantization in both brackets and the
    # elapsed-time difference (continuous timestamps occur in multiple terms).
    uncertainty_ns = (started.span_ns + finished_sample.span_ns
                      + 6 * clock.resolution_ns + 2 * clock.awake_resolution_ns)
    return {"returncode": process.returncode, "timed_out": timed_out or finished > deadline_ns,
            "wall_seconds": wall_ns / 1e9, "continuous_seconds": wall_ns / 1e9,
            "awake_seconds": awake_ns / 1e9, **clock.info(),
            "clock_gap_seconds": (wall_ns - awake_ns) / 1e9,
            "clock_gap_uncertainty_seconds": uncertainty_ns / 1e9}


def szs_result(text, returncode, timed_out):
    statuses = re.findall(r"^\s*[%#]?\s*(?:\(\d+\)\s*)?SZS status\s+(\w+)\b", text, re.M)
    unsat = {"Unsatisfiable", "Theorem", "ContradictoryAxioms"}
    sat = {"Satisfiable", "CounterSatisfiable"}
    unknown = {"Timeout", "GaveUp", "ResourceOut", "MemoryOut", "Unknown", "Incomplete"}
    found = set(statuses)
    if timed_out:
        result = "UNKNOWN"
    elif returncode < 0 or (found & unsat and found & sat) or found & {
        "Error", "InputError", "SyntaxError", "TypeError", "SemanticError", "UsageError", "Inappropriate"
    }:
        result = "ERROR"
    elif found & unsat:
        result = "UNSAT"
    elif found & sat:
        result = "SAT"
    elif statuses and statuses[-1] in unknown:
        result = "UNKNOWN"
    else:
        result = "ERROR"
    return result, "|".join(dict.fromkeys(statuses))


def command_for(name, executable, problem, seconds):
    limit = str(max(1, math.ceil(seconds)))
    flags = {
        "eprover": ["--auto", "--tstp-format", f"--cpu-limit={limit}"],
        "vampire": ["--mode", "casc", "--cores", "1", "--time_limit", limit],
        "zipperposition": ["--mode", "fo-complete-basic", "--input", "tptp",
                           "--output", "tptp", "--disable-e", "--timeout", limit],
    }
    return [str(executable), *flags[name], str(problem)]


def require_tar_filters():
    """tarfile's extraction filters reject escaping paths and links; refuse an interpreter without
    them (Python 3.12, and the security releases 3.8.17, 3.9.17, 3.10.12 and 3.11.4)."""
    if not hasattr(tarfile, "data_filter"):
        raise SetupError(
            f"Python {platform.python_version()} has no tarfile extraction filters; "
            "use Python 3.12 or later (or 3.9.17, 3.10.12, 3.11.4 or later in their series)")


def unpack(archive, destination):
    """Reject escaping paths/links before executing any downloaded code."""
    archive, destination = pathlib.Path(archive), pathlib.Path(destination)
    destination.mkdir(parents=True, exist_ok=True)
    if tarfile.is_tarfile(archive):
        require_tar_filters()
        with tarfile.open(archive) as source:
            source.extractall(destination, filter="data")
    elif zipfile.is_zipfile(archive):
        with zipfile.ZipFile(archive) as source:
            for entry in source.infolist():
                target = (destination / entry.filename).resolve()
                if not target.is_relative_to(destination.resolve()):
                    raise SetupError("archive path escapes its temporary directory")
                mode = entry.external_attr >> 16
                if mode & 0o170000 == 0o120000:
                    raise SetupError("ZIP symlinks are not supported")
                source.extract(entry, destination)
                if mode and target.is_file():
                    target.chmod(mode & 0o777)
    else:
        with archive.open("rb") as stream:
            compressed = stream.read(2) == b"\x1f\x8b"
        if compressed:
            with gzip.open(archive, "rb") as source, (destination / "binary").open("wb") as target:
                shutil.copyfileobj(source, target)
        else:
            shutil.copy2(archive, destination / "binary")


def native_binary(path, system, machine):
    description = subprocess.run(
        ["file", "-b", str(path)], check=True, capture_output=True, text=True
    ).stdout.lower()
    correct_os = "mach-o" in description if system == "darwin" else "elf" in description
    correct_arch = ("arm64" in description or "aarch64" in description) if machine == "arm64" else (
        "x86-64" in description or "x86_64" in description)
    return correct_os and correct_arch and "executable" in description


def find_binary(directory, name, target):
    candidates = sorted(
        (p for p in pathlib.Path(directory).rglob("*")
         if p.is_file() and (p.name.startswith(name) or p.name == "binary")),
        key=lambda p: (len(p.parts), len(p.name), str(p)),
    )
    for path in candidates:
        if native_binary(path, *target):
            path.chmod(path.stat().st_mode | 0o700)
            return path.resolve()
    raise SetupError(f"no native {name} executable for {'/'.join(target)} in {directory}")


@dataclass
class Tool:
    name: str
    executable: pathlib.Path
    provenance: dict


class Releases:
    def __init__(self, root, records, *, tags=None, jobs=4, setup_seconds=1800,
                 source=False, zipper_ocaml="auto"):
        self.root, self.records = pathlib.Path(root), pathlib.Path(records)
        self.tags, self.jobs = tags or {}, jobs
        self.setup_seconds, self.source, self.zipper_ocaml = setup_seconds, source, zipper_ocaml
        self.target = host_target()
        self.commands = []
        self.log = self.records / "setup.log"
        self.records.mkdir(parents=True, exist_ok=True)

    def execute(self, command, *, cwd=None, env=None, output=None, seconds=None, check=True):
        command = [str(x) for x in command]
        self.commands.append({"argv": command, "cwd": str(cwd) if cwd else None})
        with self.log.open("a") as stream:
            stream.write("\n$ " + shlex.join(command) + "\n")
        remaining = self.deadline - time.monotonic()
        if remaining <= 0:
            raise SetupError(f"setup time budget exhausted; see {self.log}")
        result = run_logged(
            command, output or self.log, min(seconds or remaining, remaining),
            cwd=cwd, env=env, stderr=self.log if output else None,
        )
        if result["timed_out"] or (check and result["returncode"] != 0):
            raise SetupError(f"command failed ({result}): {shlex.join(command)}; see {self.log}")
        return result

    def api(self, endpoint, *, missing_ok=False, paginate=False):
        output = self.root / "response.json"
        output.unlink(missing_ok=True)
        command = ["gh", "api", endpoint]
        if missing_ok:
            command.append("--include")
        if paginate:
            command.extend(["--paginate", "--slurp"])
        result = self.execute(command, output=output, seconds=60, check=False)
        response = output.read_text() if output.exists() else ""
        status = ""
        if missing_ok:
            headers, _, response = response.partition("\n\n")
            if match := re.match(r"HTTP/\S+\s+(\d{3})\b", headers):
                status = match[1]
        try:
            payload = json.loads(response)
        except json.JSONDecodeError:
            payload = None
        if result["returncode"] != 0:
            # Only an explicit HTTP 404 permits a missing-release fallback.
            # DNS, authentication, rate limits and timeouts must still fail.
            if not status and isinstance(payload, dict):
                status = str(payload.get("status", ""))
            if missing_ok and status == "404":
                return None
            raise SetupError(f"gh api {endpoint} failed (exit {result['returncode']}"
                             f"{', HTTP ' + status if status else ''}); see {self.log}")
        if payload is None:
            raise SetupError(f"invalid JSON from gh api {endpoint}; see {self.log}")
        return payload

    def select(self, name, tag):
        repo = REPOSITORIES[name]
        suffix = "tags/" + urllib.parse.quote(tag, safe="") if tag else "latest"
        release = self.api(f"repos/{repo}/releases/{suffix}", missing_ok=name == "eprover")
        if release is not None:
            if release["draft"] or (not tag and release["prerelease"]):
                raise SetupError("expected a published stable Release")
            (self.records / f"{name}-release.json").write_text(json.dumps(release, indent=2) + "\n")
            return ({"origin": "release", "tag": release["tag_name"],
                     "release_url": release["html_url"], "release_id": release["id"],
                     "published_at": release["published_at"]}, release["assets"])
        # E publishes version tags without GitHub Release objects. Keep this
        # exception explicit, and never substitute an unpinned default branch.
        pages = self.api(f"repos/{repo}/tags?per_page=100", paginate=True)
        tags = [item for page in pages for item in page]
        if tag:
            selected = next((item for item in tags if item["name"] == tag), None)
        else:
            candidates = [(tuple(map(int, match[1].split("."))), item) for item in tags
                          if (match := re.fullmatch(r"E-(\d+(?:\.\d+)+)", item["name"]))]
            selected = max(candidates, key=lambda pair: pair[0])[1] if candidates else None
        if selected is None:
            raise SetupError(f"{repo}: no GitHub Release and no "
                             f"{'matching tag ' + tag if tag else 'E-x.y[.z] version tag'}")
        (self.records / f"{name}-tag.json").write_text(json.dumps(selected, indent=2) + "\n")
        record = {"origin": "tag", "tag": selected["name"], "commit": selected["commit"]["sha"],
                  "tag_url": f"https://github.com/{repo}/tree/{urllib.parse.quote(selected['name'], safe='')}",
                  "selection_reason": "GitHub Release lookup returned HTTP 404"}
        print(f"{name}: no GitHub Release; building tag {record['tag']} "
              f"at {record['commit']}", flush=True)
        return record, []

    def source_archive(self, repo, commit, destination):
        archive = destination.with_suffix(".tar.gz")
        self.execute(["gh", "api", f"repos/{repo}/tarball/{commit}"], output=archive)
        unpack(archive, destination)
        roots = [p for p in destination.iterdir() if p.is_dir()]
        if len(roots) != 1:
            raise SetupError(f"unexpected source archive layout: {archive}")
        return roots[0], sha256(archive)

    def submodules(self, repo, commit, directory, records, depth=0):
        if not (directory / ".gitmodules").is_file():
            return
        if depth >= 8:
            raise SetupError("submodule nesting exceeds 8")
        config = configparser.ConfigParser(interpolation=None)
        config.read(directory / ".gitmodules")
        tree = self.api(f"repos/{repo}/git/trees/{commit}?recursive=1")
        if tree.get("truncated"):
            raise SetupError("GitHub truncated the submodule tree")
        links = {entry["path"]: entry["sha"] for entry in tree["tree"] if entry["mode"] == "160000"}
        for section in config.sections():
            path, url = config[section]["path"], config[section]["url"]
            # Source builds deliberately omit optional SMT support, but retain
            # the release's pinned mandatory CaDiCaL/VIRAS dependencies.
            if repo == REPOSITORIES["vampire"] and path == "z3":
                continue
            target = (directory / path).resolve()
            if target == directory.resolve() or not target.is_relative_to(directory.resolve()):
                raise SetupError("submodule path escapes its source tree")
            if path not in links:
                raise SetupError(f"missing pinned commit for submodule {path}")
            if url.startswith("."):
                url = urllib.parse.urljoin(f"https://github.com/{repo}/", url)
            url = url.replace("git@github.com:", "https://github.com/")
            match = re.fullmatch(r"https://github\.com/([\w.-]+/[\w.-]+?)(?:\.git)?/?", url)
            if not match:
                raise SetupError(f"unsupported submodule URL: {url}")
            subrepo = match[1]
            staging = self.root / ("submodule-" + str(len(records)))
            records.append({"repository": subrepo, "commit": links[path], "path": path})
            source, checksum = self.source_archive(subrepo, links[path], staging)
            records[-1]["archive_sha256"] = checksum
            if target.exists():
                target.rmdir()  # Git archive leaves either no entry or an empty directory.
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.move(source, target)
            self.submodules(subrepo, links[path], target, records, depth + 1)

    def build(self, name, directory, record):
        repo = REPOSITORIES[name]
        commit = record.get("commit") or self.api(
            f"repos/{repo}/commits/{urllib.parse.quote(record['tag'], safe='')}")["sha"]
        source, checksum = self.source_archive(repo, commit, directory / "source")
        record.update(method="source", commit=commit, archive_sha256=checksum, submodules=[])
        self.submodules(repo, commit, source, record["submodules"])
        if name == "eprover":
            self.execute(["sh", "./configure"], cwd=source)
            self.execute(["make", "-j", self.jobs], cwd=source)
            return find_binary(source / "PROVER", name, self.target)
        if name == "vampire":
            build = directory / "build"
            self.execute(["cmake", "-S", source, "-B", build, "-DCMAKE_BUILD_TYPE=Release",
                          "-DBUILD_TESTING=OFF", "-DCMAKE_DISABLE_FIND_PACKAGE_Z3=TRUE"])
            self.execute(["cmake", "--build", build, "--target", "vampire", "--parallel", self.jobs])
            return find_binary(build, name, self.target)
        env = os.environ.copy()
        for key in ("OPAMROOT", "OPAMSWITCH", "OPAM_SWITCH_PREFIX", "OCAMLPATH", "OCAMLLIB",
                    "OCAMLFIND_CONF", "CAML_LD_LIBRARY_PATH", "OCAML_TOPLEVEL_PATH", "DUNE_INSIDE_DUNE"):
            env.pop(key, None)
        env["OPAMROOT"] = str(directory / "opam")
        record["ocaml_request"] = self.zipper_ocaml
        self.execute(["opam", "init", "--bare", "--no-setup", "--yes"], env=env)
        # Resolve the compiler together with the pinned Release's dependencies.
        # Installing a compiler first fixes an invariant that may be incompatible
        # with an old Release (e.g. 2.1 requires oseq < 0.4 and OCaml < 4.13).
        self.execute(["opam", "switch", "create", "bench", "--empty",
                      "--no-switch", "--yes"], env=env)
        env["OPAMSWITCH"] = "bench"
        self.execute(["opam", "pin", "add", "--no-action", "--yes", str(source)], env=env)
        compiler = "ocaml-base-compiler"
        if self.zipper_ocaml != "auto":
            compiler += "." + self.zipper_ocaml
        bounds = ZIPPER_DEPENDENCY_BOUNDS.get(commit, [])
        record["dependency_constraints"] = list(bounds)
        self.execute(["opam", "install", "--yes", "--no-depexts", "--jobs", self.jobs,
                      *bounds, compiler, "zipperposition"], env=env)
        compiler_version = self.records / "zipperposition-ocaml.txt"
        self.execute(["opam", "var", "ocaml:version"], env=env, output=compiler_version)
        record["ocaml"] = compiler_version.read_text().strip()
        packages = self.records / "zipperposition-packages.txt"
        self.execute(["opam", "list", "--installed", "--columns=name,version", "--color=never"],
                     env=env, output=packages)
        return find_binary(directory / "opam" / "bench" / "bin", name, self.target)

    def smoke(self, name, executable):
        # Exercise the actual benchmark flags, not just --version.
        for case, text, expected in [
            ("unsat", "fof(p,axiom,p(a)).\nfof(n,axiom,~p(a)).\n", "UNSAT"),
            ("sat", "fof(p,axiom,p(a)).\n", "SAT"),
        ]:
            problem = self.root / f"{name}-{case}.p"
            problem.write_text(text)
            output = self.records / f"{name}-{case}.log"
            output.unlink(missing_ok=True)
            result = run_logged(command_for(name, executable, problem, 3), output, 5)
            text = output.read_text(errors="replace")
            actual, _ = szs_result(text, **{
                k: result[k] for k in ("returncode", "timed_out")})
            # A refutation-only strategy may legitimately give up on the SAT fixture.
            if actual != expected and not (case == "sat" and actual == "UNKNOWN"):
                diagnostic = next((line.strip() for line in text.splitlines() if line.strip()), "(no output)")
                raise SetupError(f"{name} smoke test: expected {expected}, got {actual} "
                                 f"(exit {result['returncode']}): {diagnostic[:400]}; see {output}")

    def install(self, name):
        self.deadline = time.monotonic() + self.setup_seconds
        self.commands = []
        directory = self.root / name
        directory.mkdir()
        repo, tag = REPOSITORIES[name], self.tags.get(name)
        print(f"Preparing {name}: gh Release lookup ({tag or 'latest stable'})", flush=True)
        record = {"name": name, "repository": repo, "platform": "/".join(self.target)}
        record_path = self.records / f"{name}.json"
        try:
            selected, assets = self.select(name, tag)
            record.update(selected)
            executable = None
            assets = sorted(assets, key=lambda a: (-asset_score(a["name"], *self.target), a["name"]))
            record["asset_attempts"] = []
            for asset in ([] if self.source else assets):
                if not asset_score(asset["name"], *self.target):
                    continue
                attempt = {"name": asset["name"], "id": asset["id"], "url": asset["browser_download_url"]}
                record["asset_attempts"].append(attempt)
                archive = directory / f"asset-{asset['id']}"
                extracted = directory / f"unpacked-{asset['id']}"
                self.execute(["gh", "release", "download", record["tag"], "--repo", repo,
                              "--pattern", asset["name"], "--output", archive])
                attempt["sha256"] = sha256(archive)
                if (asset.get("digest") or "").startswith("sha256:"):
                    if asset["digest"] != "sha256:" + attempt["sha256"]:
                        raise SetupError("downloaded asset does not match its Release digest")
                try:
                    unpack(archive, extracted)
                    candidate = find_binary(extracted, name, self.target)
                    self.smoke(name, candidate)
                    executable = candidate
                    record.update(method="asset", asset=attempt)
                    break
                except (SetupError, OSError, tarfile.TarError, zipfile.BadZipFile) as error:
                    attempt["rejected"] = str(error)
            if executable is None:
                print(f"Building {name} from {record['origin']} {record['tag']} in {directory}", flush=True)
                executable = self.build(name, directory, record)
                self.smoke(name, executable)
            version_log = self.records / f"{name}-version.log"
            version = run_logged([executable, "--version"], version_log, 5)
            record.update(executable=str(executable), executable_sha256=sha256(executable),
                          version_exit=version["returncode"],
                          version_output=version_log.read_text(errors="replace")[:4096], ready=True)
            return Tool(name, executable, record)
        except BaseException as error:
            record.update(ready=False, error=str(error))
            raise
        finally:
            record["commands"] = self.commands
            record_path.write_text(json.dumps(record, indent=2) + "\n")


@contextlib.contextmanager
def temporary_tools(keep=False):
    template = str(pathlib.Path(tempfile.gettempdir()) / "axiom-atp.XXXXXX")
    root = pathlib.Path(subprocess.check_output(["mktemp", "-d", template], text=True).strip()).resolve()
    print(f"Temporary external projects: {root}", flush=True)
    try:
        yield root
    finally:
        if keep:
            print(f"Kept external projects: {root}", flush=True)
        else:
            shutil.rmtree(root)
