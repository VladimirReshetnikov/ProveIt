#!/usr/bin/env python3
"""Recalculate compatible prior bounds and a limited schedule-model scan.

Floating-point displays here are not proof-assistant certificates or finite
guards for running the asymptotic SAT algorithm. Exact formulas are in the
report. The two-stage search is only over the explicitly stated model.
"""
import argparse
import json
from math import log,log2,pi,sqrt
from pathlib import Path


def calculate():
    asym=pi*sqrt(5/2)*(9+sqrt(3))/log(2)
    combined=asym*sqrt(3)/2
    c=2/16
    A0=.1/(2*log2(16))
    k=pi*sqrt(2*(1-1/16))/log(2)
    boundary=k/sqrt(A0)*(1+c/(1-c**(2/3))**1.5)
    K0=9*pi*sqrt(2)/log(2)
    cache=sqrt(30/256)
    block=sqrt(150/256)
    omega=log2(7)
    strassen=sqrt((170-(1-(omega-2)**2)*50)/256)
    storage=sqrt(120/256)
    if not (cache+strassen*sqrt(3)/12 < strassen and
            cache*(1+sqrt(3)/9) < strassen and strassen>block):
        raise ArithmeticError("root-dominance inequality failed")
    best=None
    for r0 in range(3,301):
        for rt in range(3,301):
            root_cap=.1/(2*log2(r0))
            total=.1/log2(rt)
            k0=pi*sqrt(2*(1-1/r0))/log(2)
            kt=pi*sqrt(2*(1-1/rt))/log(2)*(2/r0)/(1-(2/rt)**(2/3))**1.5
            unconstrained=total*k0**(2/3)/(k0**(2/3)+kt**(2/3))
            u0=min(root_cap,unconstrained)
            if u0>=total:continue
            value=k0/sqrt(u0)+kt/sqrt(total-u0)
            row={"coefficient":value,"root_alphabet":r0,"tail_alphabet":rt,
                 "root_budget":u0,"tail_budget":total-u0}
            if best is None or value<best["coefficient"]:best=row
    return {"scope":"Compatible existing ingredients; no new SAT order or global optimum claimed.",
            "asymmetric_individual":asym,"composed_polynomial_space":combined,
            "fixed_r16_boundary_infimum":boundary,
            "composed_more_memory_time":K0*strassen,
            "composed_more_memory_space":K0*storage,
            "root_scale":K0,"cache_factor":cache,"table_factor":block,
            "strassen_factor":strassen,"space_factor":storage,
            "two_stage_scan":{"range":[3,300],"status":"schedule-model numerical infimum only","best":best}}


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--output",type=Path)
    args=parser.parse_args()
    result=calculate()
    serialized=json.dumps(result,indent=2)+"\n"
    if args.output:
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(serialized)
    print(serialized,end="")


if __name__=="__main__":main()
