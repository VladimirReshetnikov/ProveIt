"""Remeasure frozen complete programs, then rerun the scoped finite checks."""
import gzip
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("source_measure", ROOT / "source_measure.py")
measure = importlib.util.module_from_spec(spec)
spec.loader.exec_module(measure)
rows = json.loads((ROOT / "metrics.json").read_text())
fields = ("normalized_tokens", "ast_nodes", "normalized_bytes", "raw_bytes",
          "gzip9_raw_bytes", "gzip9_normalized_bytes", "sha256")
for row in rows:
    data = (ROOT / row["file"]).read_bytes()
    actual = measure.metrics(data)
    if any(actual[key] != row[key] for key in fields):
        raise SystemExit("Measurement mismatch: " + row["file"])
    gz = (ROOT / row["file"]).with_suffix(".py.gz")
    if gz.exists() and gz.read_bytes() != gzip.compress(data, compresslevel=9, mtime=0):
        raise SystemExit("Gzip mismatch: " + row["file"])
for name in ("test_checkers.py", "independent_audit.py"):
    subprocess.run([sys.executable, str(ROOT/name)], cwd=ROOT, check=True)
print("All frozen measurements and scoped finite checks passed.")
