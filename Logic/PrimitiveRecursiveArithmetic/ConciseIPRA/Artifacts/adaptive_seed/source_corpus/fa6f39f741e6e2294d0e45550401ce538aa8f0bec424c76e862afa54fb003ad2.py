"""Verify inherited appendix identity and reproduce the packaged checker evidence."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
provenance = json.loads((ROOT / "evidence/inherited_arithmetic.json").read_text())
for item in provenance["sources"]:
    path = ROOT / item["local_file"]
    if hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
        raise SystemExit("Changed inherited arithmetic source: " + item["local_file"])
subprocess.run([sys.executable, str(ROOT / "implementation/verify.py")],
               cwd=ROOT / "implementation", check=True)
print("Inherited arithmetic source hashes and complete implementation evidence passed.")
