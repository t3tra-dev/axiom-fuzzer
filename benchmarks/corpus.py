"""Small, attributed application corpus; expand only the bundled TPTP includes."""
import hashlib
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parent / "problems"
INCLUDE = re.compile(r"\s*include\('([^']+)'\)\.\s*")
FORMULA = re.compile(r"^\s*(?:fof|cnf)\(", re.MULTILINE)


def applications(root=ROOT):
    manifest = json.loads((root / "manifest.json").read_text())
    files = {}
    for name, record in manifest["files"].items():
        path = (root / "tptp" / name).resolve()
        if not path.is_relative_to((root / "tptp").resolve()):
            raise ValueError(f"TPTP path escapes the bundled corpus: {name}")
        data = path.read_bytes()
        if hashlib.sha256(data).hexdigest() != record["sha256"]:
            raise ValueError(f"bundled TPTP checksum mismatch: {name}")
        files[name] = data.decode("utf-8")

    def expand(name, used, stack=()):
        if name in stack or name not in files:
            raise ValueError(f"unbundled or cyclic TPTP include: {name}")
        used.add(name)
        lines = []
        for line in files[name].splitlines(keepends=True):
            include = INCLUDE.fullmatch(line)
            if include:
                lines.append(expand(include[1], used, (*stack, name)))
            elif re.match(r"\s*include\s*\(", line):
                raise ValueError(f"unsupported TPTP include syntax in {name}")
            else:
                lines.append(line)
        return "".join(lines)

    result = []
    hashes = set()
    for problem in manifest["problems"]:
        name = problem["file"]
        expected = {"SAT": "Satisfiable", "UNSAT": "Unsatisfiable"}[problem["expected"]]
        if not re.search(r"^% Status\s*:\s*" + expected + r"\s*$", files[name], re.MULTILINE):
            raise ValueError(f"TPTP status does not match the manifest: {name}")
        used = set()
        text = expand(name, used)
        digest = hashlib.sha256(text.encode()).hexdigest()
        if digest in hashes:
            raise ValueError(f"duplicate application input: {name}")
        hashes.add(digest)
        result.append({
            **problem, "text": text, "axioms": len(FORMULA.findall(text)),
            "library": manifest["library"],
            "library_version": manifest["files"][name].get("library_version", manifest["version"]),
            "problem_source": manifest["files"][name]["source_url"],
            "source_commit": manifest["files"][name].get("source_commit", manifest["commit"]),
            "source_files": {p: manifest["files"][p] for p in sorted(used)},
            "preparation": "Expand complete include files in place; preserve formula order and text.",
        })
    return result
