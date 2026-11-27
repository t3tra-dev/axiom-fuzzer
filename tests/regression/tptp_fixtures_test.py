"""The TPTP files of the OCaml tests are verbatim files of the release their manifest names.

tests/fixtures/tptp/manifest.json lists every file under Problems/ and Axioms/ with its release
and SHA-256; each file's header names that release, and every include directive names a listed
file, so that the tests can read the problems as they are.
"""
import hashlib
import json
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1])
manifest = json.loads((root / "manifest.json").read_text())
listed = manifest["files"]
present = {str(p.relative_to(root)) for d in ("Problems", "Axioms") for p in (root / d).rglob("*")
           if p.is_file()}
assert present == set(listed), f"files and manifest differ: {sorted(present ^ set(listed))}"
for name, entry in listed.items():
    data = (root / name).read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry["sha256"], f"{name} is not the listed file"
    text = data.decode("ascii")
    stem = pathlib.Path(name).stem
    assert f"% File     : {stem} : TPTP v{entry['release']}." in text, f"{name}: release"
    for included in re.findall(r"^include\('([^']+)'\)\.", text, re.MULTILINE):
        assert included in listed, f"{name} includes {included}, which is not listed"
print(f"ok  {len(listed)} TPTP fixture files match their manifest")
