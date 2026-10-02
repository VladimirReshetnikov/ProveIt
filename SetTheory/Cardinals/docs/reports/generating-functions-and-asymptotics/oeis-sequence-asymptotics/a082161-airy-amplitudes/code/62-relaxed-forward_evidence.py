#!/usr/bin/env python3
"""Floating-point forward recurrence evidence; never a gamma enclosure.

The normalized array is d[N,j]/2**N. Cost is O(max_n**2) arithmetic and
O(max_n) storage. Underflow and roundoff limit very large requested sizes.
"""
if not __debug__:
    raise RuntimeError("Run with assertions enabled; do not use python -O")

import argparse
import json
import math
from pathlib import Path

import numpy as np
from scipy.special import ai_zeros


def evaluate(max_n):
    if max_n < 1:
        raise ValueError("--max-n must be positive")
    z = float(ai_zeros(1)[0][0])
    L1, L2, L3 = 53*z*z/90, 44*z/27, 141/140-1304*z**3/42525
    c1, c2, c3 = L1, L2+L1**2/2, L3+L1*L2+L1**3/6
    markers = {n for n in (10,100,300,1000,3000,10000,20000,max_n) if n <= max_n}
    v = np.zeros(2*max_n+3, dtype=np.float64)
    v[0] = 1
    rows = []
    for N in range(1, 2*max_n+1):
        j = np.arange(N%2,N+1,2)
        new = np.zeros(N+2, dtype=np.float64)
        new[j] = 0.5*v[j+1]
        positive = j[j>0]
        new[positive] += 0.5*(N-positive+2)/(N+positive)*v[positive-1]
        v[:N+2] = new
        if N%2 == 0 and N//2 in markers:
            n = N//2
            if not v[0] > 0:
                raise ArithmeticError(f"Endpoint underflow at n={n}; floating-point evidence unavailable")
            t = n**(-1/3)
            # Log arithmetic avoids an unnecessary overflow in exp(-3*z*n^(1/3)).
            raw = math.exp(math.log(float(v[0]))-3*z*n**(1/3)-math.log(n))
            row = {"n":n, "raw_amplitude":raw,
                   "relative_three_corrections":raw/(1+c1*t+c2*t*t+c3*t**3),
                   "logarithmic_three_corrections":raw*math.exp(-L1*t-L2*t*t-L3*t**3)}
            assert all(math.isfinite(value) for value in row.values())
            rows.append(row)
            print(json.dumps(row), flush=True)
    return {"passed":True,"max_n":max_n,"dtype":"numpy.float64",
            "forward_relative_coefficients":[c1,c2,c3],
            "forward_log_coefficients":[L1,L2,L3],"numerics":rows,
            "limitation":"Floating-point evidence, not exact recurrence evaluation, a gamma enclosure, or an analytic proof"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n",type=int,default=20000)
    parser.add_argument("--output",type=Path,default=Path(__file__).resolve().parent/"output"/"forward_evidence.json")
    args=parser.parse_args()
    result=evaluate(args.max_n)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n")


if __name__ == "__main__":
    main()
