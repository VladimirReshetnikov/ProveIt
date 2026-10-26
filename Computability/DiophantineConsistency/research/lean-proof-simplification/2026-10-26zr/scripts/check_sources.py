#!/usr/bin/env python3
"""Verify the pinned source inputs. Does not modify the supplied checkout."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("repository", type=Path, help="Root of a ProveIt checkout")
args = parser.parse_args()
packet = Path(__file__).resolve().parent.parent
manifest = json.loads((packet / "evidence/source_manifest.json").read_text())
failures = []
for item in manifest["files"]:
    target = args.repository / item["path"]
    if not target.is_file():
        failures.append(f"MISSING {item['path']}")
        continue
    actual = hashlib.sha256(target.read_bytes()).hexdigest()
    if actual != item["sha256"]:
        failures.append(f"MISMATCH {item['path']}: {actual}")
if failures:
    print("\n".join(failures))
    raise SystemExit(1)
print(f"All {len(manifest['files'])} source hashes match revision {manifest['revision']}.")
