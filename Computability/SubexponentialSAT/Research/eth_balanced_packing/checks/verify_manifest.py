#!/usr/bin/env python3
"""Verify the released files against MANIFEST.sha256.json."""
from pathlib import Path
import hashlib, json
ROOT=Path(__file__).resolve().parents[1]
records=json.loads((ROOT/"MANIFEST.sha256.json").read_text())
failures=[]
for relative,expected in records.items():
    target=ROOT/relative
    if not target.is_file():
        failures.append(relative+": missing")
    elif hashlib.sha256(target.read_bytes()).hexdigest()!=expected:
        failures.append(relative+": changed")
if failures:
    raise SystemExit("\n".join(failures))
print(f"Verified {len(records)} release files.")
