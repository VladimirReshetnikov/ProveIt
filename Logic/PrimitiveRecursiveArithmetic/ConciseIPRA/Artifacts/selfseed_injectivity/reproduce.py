"""Run the included verification suites; optionally rebuild the PDF or Lean theorem."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--lean", help="Lean 4.24.0 executable; otherwise use lean on PATH if present")
parser.add_argument("--pdf", action="store_true", help="Recompile the report from installed TeX")
parser.add_argument("--manifest-only", action="store_true")
args = parser.parse_args()

if args.manifest_only:
    entries = (ROOT / "MANIFEST.sha256").read_text().splitlines()
    for entry in entries:
        digest, path = entry.split("  ", 1)
        actual = hashlib.sha256((ROOT / path).read_bytes()).hexdigest()
        if actual != digest:
            raise SystemExit("Checksum mismatch: " + path)
    print("Verified", len(entries), "artifact checksums.")
    raise SystemExit(0)

for part in ("compact", "selfseed"):
    subprocess.run([sys.executable, str(ROOT / part / "verify.py")], cwd=ROOT, check=True)

selfseed = json.loads((ROOT / "selfseed/verification.json").read_text())
compact = json.loads((ROOT / "compact/evidence/verification.json").read_text())
(ROOT / "selfseed/metrics.json").write_text(json.dumps(selfseed["metrics"], indent=2) + "\n")
receipt = {
    "python": sys.version,
    "selfseed": {"executions": selfseed["executions"], "unexpected_outcomes": selfseed["unexpected_outcomes"]},
    "compact_receipt": "compact/evidence/verification.json",
    "compact_metrics": compact.get("metrics"),
    "lean_scope": "Abstract stopping-orbit core only; written report derives its hypotheses in T_F^-."
}
lean = args.lean or shutil.which("lean")
if lean:
    result = subprocess.run([lean, str(ROOT / "formal/StoppingOrbits.lean")],
                            cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    if "does not depend on any axioms" not in result.stdout:
        raise SystemExit("Expected Lean axiom audit missing.")
    receipt["lean"] = {
        "version": subprocess.check_output([lean, "--version"], text=True).strip(),
        "exit_code": result.returncode,
        "stdout": result.stdout.strip(),
        "stderr": result.stderr,
        "source_sha256": hashlib.sha256((ROOT / "formal/StoppingOrbits.lean").read_bytes()).hexdigest()
    }
else:
    receipt["lean"] = {"executed": False, "reason": "Lean not on PATH; an earlier compiled receipt is included."}
if args.pdf:
    subprocess.run([sys.executable, str(ROOT / "build_pdf.py"),
                    "--tex", str(ROOT / "selfseed_ipra.tex"),
                    "--output", str(ROOT / "selfseed_ipra.pdf"),
                    "--log", str(ROOT / "evidence/pdf_build.log")], check=True)
(ROOT / "evidence/reproduction.json").write_text(json.dumps(receipt, indent=2) + "\n")
print(json.dumps(receipt, indent=2))

