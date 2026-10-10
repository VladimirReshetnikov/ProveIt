"""Read-only check that the proposed source patch matches its pinned baseline."""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess

root=Path(__file__).resolve().parents[1]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("repository",type=Path)
args=parser.parse_args()
provenance=json.loads((root/"provenance.json").read_text())
names=["Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex",
       "Analysis/Polylogarithms/docs/manuscript/chapters/06-cm.tex"]
for name in names:
    actual=hashlib.sha256((args.repository/name).read_bytes()).hexdigest()
    if actual!=provenance["source_files_sha256"][name]:
        raise SystemExit(f"Source hash differs from the pinned baseline: {name}")
subprocess.run(["git","apply","--check",str(root/"corrections/proposed_corrections.diff")],
               cwd=args.repository,check=True)
print("Both pinned file hashes match; git apply --check passed. No files changed.")
