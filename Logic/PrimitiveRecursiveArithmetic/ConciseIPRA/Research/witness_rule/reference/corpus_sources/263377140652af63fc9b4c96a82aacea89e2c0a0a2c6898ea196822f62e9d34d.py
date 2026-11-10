"""Verify the delivered payload, then rerun finite evidence in a temporary copy."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
manifest = ROOT / "MANIFEST.json"
if manifest.exists():
    for row in json.loads(manifest.read_text())["files"]:
        data = (ROOT / row["path"]).read_bytes()
        if len(data) != row["bytes"] or hashlib.sha256(data).hexdigest() != row["sha256"]:
            raise SystemExit("Manifest mismatch: " + row["path"])
    print("Distributed payload hashes verified.", flush=True)
with tempfile.TemporaryDirectory(prefix="ipra-reproduce-") as folder:
    target = Path(folder) / "package"
    shutil.copytree(ROOT, target, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    for entry in ("implementation/reproduce.py", "code/verify_progressive_separator.py",
                  "code/verify_zero_profiles.py"):
        subprocess.run([sys.executable, str(target / entry)], cwd=target, check=True)
print("All recorded source measurements and finite checks passed.")
