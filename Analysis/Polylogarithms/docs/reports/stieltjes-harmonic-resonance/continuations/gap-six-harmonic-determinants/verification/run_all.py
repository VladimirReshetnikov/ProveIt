#!/usr/bin/env python3
"""Run the delivered mathematical verification programs, saving every log."""
from pathlib import Path
import subprocess
import sys
import time
import json

HERE=Path(__file__).resolve().parent
OUT=HERE.parent/"results"
OUT.mkdir(exist_ok=True)
SCRIPTS=["verify_gap_six.py","create_gap_six_example.py","verify_complex_rank.py",
         "verify_hahn_polylogs.py","derive_euler_endpoint.py","verify_collisions.py",
         "verify_gap_six_audit.py","verify_collision_audit.py"]
records=[]
for name in SCRIPTS:
    start=time.perf_counter()
    proc=subprocess.run([sys.executable,str(HERE/name)],cwd=HERE.parent,
                        stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
    (OUT/(Path(name).stem+".log")).write_text(proc.stdout)
    record={"script":name,"exit_code":proc.returncode,
            "elapsed_seconds":round(time.perf_counter()-start,3)}
    records.append(record)
    print(json.dumps(record),flush=True)
    (OUT/"verification_run.json").write_text(json.dumps(records,indent=2)+"\n")
    if proc.returncode:
        print(proc.stdout[-6000:])
        raise SystemExit(proc.returncode)
print("All delivered verification programs passed.")
