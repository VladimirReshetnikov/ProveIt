#!/usr/bin/env python3
"""Verify the source pins and five theorem exports given a grh-lean checkout."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root = Path(sys.argv[1]).resolve()
commit = subprocess.check_output(["git","-C",str(root),"rev-parse","HEAD"],text=True).strip()
assert commit == "72fead102f663d5c7a407964a13dc0cf9d977207"
names = ("riemannHypothesis","riemannZeta_eq_zero_re","LFunction_ne_zero_of_half_lt_re",
         "LFunction_eq_zero_re","LFunction_eq_zero_re_of_isPrimitive")
fingerprints = []
for edition in ("grh","grh-compact"):
    base = root / edition
    assert (base/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0"
    packages = json.loads((base/"lake-manifest.json").read_text())["packages"]
    assert next(p["rev"] for p in packages if p["name"] == "mathlib") == "56a005855ea17e0b0958f73ec801ae140b0a1679"
    declarations = re.findall(r"^theorem (\w+)",(base/"src/Main.lean").read_text(),re.M)
    assert all(name in declarations for name in names)
    assert (base/"scripts/PrintAxioms.lean").read_text().count("#print axioms") == 5
    statements = (base/"src/Statements.lean").read_bytes()
    assert statements.startswith(b"import Mathlib\n")
    fingerprints.append(hashlib.sha256(statements).hexdigest())
assert fingerprints[0] == fingerprints[1]
print(f"Revision {commit}; both sets of five exports and dependency pins matched.")
print(f"Identical statement files, SHA-256 {fingerprints[0]}.")
