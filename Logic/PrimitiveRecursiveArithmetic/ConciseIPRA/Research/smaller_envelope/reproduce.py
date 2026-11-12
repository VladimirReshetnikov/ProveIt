"""Reproduce measurements and focused implementation checks."""
from pathlib import Path
import json
import subprocess
import sys

root = Path(__file__).resolve().parent
for script in ["measure.py", "validation/validate_inferred.py",
               "validation/validate_bytes.py", "validation/validate_strict.py"]:
    print("Running " + script, flush=True)
    subprocess.run([sys.executable, str(root / script)], cwd=root, check=True)
summary = {
    "metrics": json.loads((root / "evidence/METRICS.json").read_text()),
    "inferred": json.loads((root / "evidence/inferred_summary.json").read_text()),
    "bytes": json.loads((root / "evidence/byte_validation.json").read_text()),
    "strict": json.loads((root / "evidence/strict_validation.json").read_text()),
    "limits": "Finite executable checks; mathematical proofs are in the report."
}
(root / "evidence/REPRODUCTION.json").write_text(json.dumps(summary, indent=2) + "\n")
print("All measurements and focused implementation checks passed.")
