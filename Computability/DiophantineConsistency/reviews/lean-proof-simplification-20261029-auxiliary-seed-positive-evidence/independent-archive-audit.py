#!/usr/bin/env python3
"""Check the archived receipts and their connection to the committed source."""
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
source_path = "Computability/DiophantineConsistency/Lean/DiophantineConsistency/ArithmeticPellAuxiliarySeed.lean"
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
        committed = subprocess.check_output(["git", "show", f"{revision}:{source_path}"])
        assert z.read(f"commit/{role}.lean") == committed
        assert z.read(f"prototype/{role}/DiophantineConsistency/ArithmeticPellAuxiliarySeed.lean") == committed
    assert z.read("independent/review.txt") == (root / review["file"]).read_bytes()
    assert "prototype/final/DiophantineConsistency/ArithmeticPellAuxiliarySeedChecks.lean" in z.namelist()
print(f"PASS: {len(manifest['members'])} archive members, CRC, checksums, review, source snapshots and commits")
