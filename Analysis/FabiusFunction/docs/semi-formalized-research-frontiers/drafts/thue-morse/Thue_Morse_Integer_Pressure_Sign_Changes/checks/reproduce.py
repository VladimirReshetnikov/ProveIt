#!/usr/bin/env python3
"""Rebuild every exact finite row in a separate replay directory."""
from pathlib import Path
import concurrent.futures, subprocess, json
ROOT=Path(__file__).resolve().parent
OUT=ROOT/"replay";OUT.mkdir(exist_ok=True)
EXE=OUT/"first_negative_exact"
subprocess.run(["g++","-O2","-std=c++17",str(ROOT/"first_negative_exact.cpp"),"-lgmpxx","-lgmp","-o",str(EXE)],check=True)
def run(m):
    output=OUT/f"m{m:03d}.json"
    subprocess.run([str(EXE),str(m),str(5*m),str(output)],check=True,capture_output=True,text=True)
    a=json.loads(output.read_text());b=json.loads((ROOT/f"m{m:03d}.json").read_text())
    for key in ("m","checked_through_degree","exact_fourier_residuals","first_post_cancellation_negative_degree","normalized_eigenvalue_even_coefficients","pressure_even_coefficients"):
        if a[key]!=b[key]:raise ArithmeticError(f"m={m}, field={key}")
    return m
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
    orders=list(pool.map(run,range(2,21)))
print(json.dumps({"passed":True,"orders":orders,"exact_fourier_residuals":sum(10*m for m in orders)}))

