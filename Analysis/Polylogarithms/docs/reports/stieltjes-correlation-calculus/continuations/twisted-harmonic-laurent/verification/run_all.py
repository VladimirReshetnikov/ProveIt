#!/usr/bin/env python3
"""Replay every delivered analytic diagnostic and exact finite check.

No network access is used.  This overwrites the associated JSON results;
use a copy of the package to preserve the original recorded evidence.
"""
from pathlib import Path
import json
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]
SCRIPTS=[
 "code/verify_periodic_calculus.py",
 "code/verify_twisted_calculus.py",
 "verification/harmonic_coefficients.py",
 "verification/harmonic_mellin_numeric.py",
 "verification/additional_numeric.py",
]
runs=[]
for script in SCRIPTS:
    print("Running "+script,flush=True)
    start=time.perf_counter()
    proc=subprocess.run([sys.executable,str(ROOT/script)],cwd=ROOT,
                        text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    elapsed=time.perf_counter()-start
    print(proc.stdout,flush=True)
    runs.append(dict(script=script,returncode=proc.returncode,
                     elapsed_seconds=round(elapsed,3),stdout=proc.stdout))
    report=dict(all_passed=all(x["returncode"]==0 for x in runs),
                complete=len(runs)==len(SCRIPTS),python=platform.python_version(),runs=runs)
    (ROOT/"verification/replay_run.json").write_text(json.dumps(report,indent=2)+"\n")
    if proc.returncode:
        raise SystemExit(proc.returncode)
print("All five replay scripts passed.",flush=True)

