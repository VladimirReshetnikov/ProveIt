#!/usr/bin/env python3
"""Replay all six packaged verification programs and record their results."""
import json
import platform
from pathlib import Path
import subprocess
import sys
import time
import sympy
import mpmath

if sys.flags.optimize:
    raise RuntimeError("Run the verification without disabling Python assertions.")

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = [
    "verify_gap_four.py",
    "verify_complementary.py",
    "verify_telescoping.py",
    "verify_gamma_sectors.py",
    "verify_higher_resonance.py",
    "verify_logarithmic_spectral.py",
]
log_dir = ROOT / "data" / "replay"
log_dir.mkdir(parents=True, exist_ok=True)
record = {"python": platform.python_version(), "sympy": sympy.__version__,
          "mpmath": mpmath.__version__, "scripts": []}
for name in SCRIPTS:
    started = time.monotonic()
    process = subprocess.run([sys.executable, str(ROOT / "verification" / name)],
                             cwd=ROOT, capture_output=True, text=True)
    elapsed = time.monotonic() - started
    log_path = log_dir / (Path(name).stem + ".log")
    log_path.write_text(process.stdout + process.stderr)
    record["scripts"].append({"script": name, "exit_code": process.returncode,
                              "elapsed_seconds": round(elapsed, 3),
                              "log": str(log_path.relative_to(ROOT))})
    print(f"{name}: {'PASS' if process.returncode == 0 else 'FAIL'} ({elapsed:.2f}s)", flush=True)
    if process.returncode:
        record["all_passed"] = False
        (ROOT / "data" / "replay_summary.json").write_text(json.dumps(record, indent=2) + "\n")
        print((process.stdout + process.stderr)[-6000:], file=sys.stderr)
        raise SystemExit(process.returncode)
record["all_passed"] = True
(ROOT / "data" / "replay_summary.json").write_text(json.dumps(record, indent=2) + "\n")
print("All exact checks and numerical diagnostics passed.")
