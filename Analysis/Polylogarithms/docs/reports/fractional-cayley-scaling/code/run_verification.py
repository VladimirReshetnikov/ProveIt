#!/usr/bin/env python3
"""Replay the exact mathematical certificates; optionally run diagnostics.

Run from any directory. Output is stored in data/ and verification/.
Subprocesses use this interpreter, so an activated environment is honored.
"""
import argparse
import importlib.metadata
import json
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--diagnostics",action="store_true")
    args=parser.parse_args()
    out=ROOT/"verification";out.mkdir(exist_ok=True)
    logs=out/"logs";logs.mkdir(exist_ok=True)
    for name in ["cayley","zeros","kernels"]:(ROOT/"data"/name).mkdir(exist_ok=True)
    jobs=[
        ("local_radius_exact",["code/verify_local_radius.py"],ROOT,"exact rational polynomial certificates"),
        ("gamma_exact",["code/verify_gamma_transition.py"],ROOT,"exact moments and coefficient identities"),
        ("zero_signs_exact",["code/zeros/verify_zeros.py","--output",str(ROOT/"data/zeros")],ROOT,"exact rational interval sign certificates"),
        ("bessel_coefficients_exact",["code/zeros/bessel_coefficients.py","--order","4","--output",str(ROOT/"data/zeros/bessel-coefficients.json")],ROOT,"exact rational-polynomial coefficient generation"),
        ("cayley_ranks_exact",["code/cayley/check_cayley_ranks.py"],ROOT/"data/cayley","all prescribed rational matrices through weight four"),
        ("harmonic_cayley_exact",["code/cayley/verify_harmonic_cayley.py"],ROOT/"data/cayley","eight exact word-identity residuals"),
    ]
    turning=ROOT/"code/kernels/certify_fractional_turning.py"
    if turning.exists():jobs.append(("fractional_turning_exact",[str(turning)],ROOT,"exact rational interval signs for the fractional maximum branch"))
    minimum=ROOT/"code/kernels/certify_fractional_minimum.py"
    if minimum.exists():jobs.append(("fractional_minimum_exact",[str(minimum)],ROOT,"exact rational interval signs for the complementary fractional minimum branch"))
    if args.diagnostics:
        jobs.extend([
            ("kernel_diagnostics",["code/kernels/check_subunit_kernel.py","--output",str(ROOT/"data/kernels/subunit_diagnostics.json")],ROOT,"floating point diagnostics at 80 decimal digits"),
            ("bessel_diagnostics",["code/zeros/verify_zeros.py","--diagnostics","--output",str(ROOT/"data/zeros")],ROOT,"floating point diagnostics at 250 decimal digits, plus exact signs"),
            ("gamma_diagnostics",["code/verify_gamma_transition.py","--diagnostics"],ROOT,"floating point improper quadrature at 65 decimal digits, plus exact algebra"),
        ])
    results=[]
    for name,cmd,cwd,scope in jobs:
        command=[sys.executable,str(ROOT/cmd[0])]+cmd[1:]
        start=time.monotonic()
        proc=subprocess.run(command,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        (logs/f"{name}.txt").write_text(proc.stdout)
        row={"name":name,"exit_code":proc.returncode,"seconds":round(time.monotonic()-start,3),"scope":scope,"log":f"verification/logs/{name}.txt"}
        results.append(row)
        print(f"{'PASS' if proc.returncode==0 else 'FAIL'} {name} ({row['seconds']} s)",flush=True)
        if proc.returncode:print(proc.stdout[-6000:],flush=True)
    versions={"python":platform.python_version()}
    for package in ["sympy","mpmath","numpy","matplotlib"]:
        try:versions[package]=importlib.metadata.version(package)
        except importlib.metadata.PackageNotFoundError:versions[package]="not installed"
    result={"status":"PASS" if all(v["exit_code"]==0 for v in results) else "FAIL","diagnostics_requested":args.diagnostics,"software":versions,"jobs":results,"scope_note":"Exact finite algebra and interval results audit the written analytic proofs. Floating point jobs are labeled diagnostics and do not certify their decimal outputs."}
    filename="replay_with_diagnostics.json" if args.diagnostics else "replay_exact.json"
    (out/filename).write_text(json.dumps(result,indent=2)+"\n")
    print(f"{result['status']}: {len(jobs)} verification jobs",flush=True)
    raise SystemExit(0 if result["status"]=="PASS" else 1)


if __name__=="__main__":main()
