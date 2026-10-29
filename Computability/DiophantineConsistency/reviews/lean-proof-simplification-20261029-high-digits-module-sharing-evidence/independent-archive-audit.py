#!/usr/bin/env python3
"""Check archived receipts and the three changed plus one new source module."""
import hashlib
import json
from pathlib import Path
import subprocess
import zipfile

root = Path(__file__).resolve().parent
manifest = json.loads((root / "BUNDLE.json").read_text())
digest = lambda data: hashlib.sha256(data).hexdigest()
archive = root / manifest["archive"]
assert digest(archive.read_bytes()) == manifest["archive_sha256"]
review = manifest["independent_review"]
assert digest((root / review["file"]).read_bytes()) == review["sha256"]
source_dir = "Computability/DiophantineConsistency/Lean/DiophantineConsistency"
modules = ("ArithmeticCellLocal", "CurrentHighDigits2011", "MFCurrentHighDigits2011")
new_module = "CurrentHighDigitFacts2011"
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    assert len(z.namelist()) == len(set(z.namelist()))
    assert set(z.namelist()) == set(manifest["members"])
    for name, metadata in manifest["members"].items():
        assert not name.startswith("/") and ".." not in Path(name).parts
        data = z.read(name)
        assert len(data) == metadata["bytes"] and digest(data) == metadata["sha256"], name
    for role, revision in (("baseline", manifest["source_parent"]),
                           ("final", manifest["source_commit"])):
        for module in modules + ((new_module,) if role == "final" else ()):
            name = module + ".lean"
            committed = subprocess.check_output(["git", "show", f"{revision}:{source_dir}/{name}"])
            assert z.read(f"commit/{role}/{name}") == committed
            assert z.read(f"selected/{role}/DiophantineConsistency/{name}") == committed
    missing = subprocess.run(["git", "cat-file", "-e", f"{manifest['source_parent']}:{source_dir}/{new_module}.lean"],
                             stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
    assert missing.returncode != 0
    assert z.read("independent/review.txt") == (root / review["file"]).read_bytes()
print(f"PASS: {len(manifest['members'])} members, CRC, checksums, review, seven source snapshots")
