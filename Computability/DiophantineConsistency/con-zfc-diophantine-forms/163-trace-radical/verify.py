#!/usr/bin/env python3
"""Check the complete frozen release; no external Python packages required."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parent

def check_manifest():
    path=ROOT/"MANIFEST_SHA256.json"
    if not path.exists():
        return {"status":"not yet sealed"}
    entries=json.loads(path.read_text())
    for item in entries["files"]:
        file=ROOT/item["path"]
        if not file.is_file() or hashlib.sha256(file.read_bytes()).hexdigest()!=item["sha256"]:
            raise ValueError("Manifest mismatch: "+item["path"])
    return {"status":"PASS","files":len(entries["files"])}

def run_job(job):
    name, relative, flags, script, extra=job
    command=[sys.executable,"-B",*flags,script,*extra]
    p=subprocess.run(command,cwd=ROOT/relative,capture_output=True,text=True)
    if p.returncode:
        raise ValueError(name+" failed:\n"+p.stdout+"\n"+p.stderr)
    try:
        detail=json.loads(p.stdout)
    except json.JSONDecodeError:
        detail={"output_sha256":hashlib.sha256(p.stdout.encode()).hexdigest()}
    return name,{"status":"PASS","result":detail}

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--rebuild",action="store_true")
    ap.add_argument("--receipt",type=Path)
    args=ap.parse_args()
    start=time.monotonic()
    manifest=check_manifest()
    jobs=[
        ("direct_normal","direct",[],"code/verify.py",["--full"]),
        ("direct_optimized","direct",["-O"],"code/verify.py",["--full"]),
        ("compact_normal","compact",[],"verify.py",[]),
        ("compact_optimized","compact",["-O"],"verify.py",[]),
        ("coefficient_reconstruction","compact/inherited/lucas/parent",[],"rebuild_coefficients.py",[]),
        ("report_literal_inputs",".",[],"code/report_inputs.py",["--check"]),
        ("compact_rebuild","compact",[],"build.py",["--check"]),
    ]
    with ThreadPoolExecutor(max_workers=3) as pool:
        results=dict(pool.map(run_job,jobs))
    if args.rebuild:
        name,result=run_job(("direct_rebuild","direct",[],"code/rebuild.py",[]))
        results[name]=result
    receipt={
        "status":"PASS","seconds":round(time.monotonic()-start,3),
        "manifest":manifest,"checks":results,
        "scope":"Exact finite artifact verification. The ordinary unbounded mathematical proofs and inherited ZFC calibration are separate."
    }
    if args.receipt:
        args.receipt.write_text(json.dumps(receipt,indent=2,sort_keys=True)+"\n")
    print(json.dumps({"status":"PASS","seconds":receipt["seconds"],
        "checks":list(results),"manifest":manifest},indent=2))

if __name__=="__main__":
    main()
