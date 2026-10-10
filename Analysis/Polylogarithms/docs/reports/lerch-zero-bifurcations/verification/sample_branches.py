#!/usr/bin/env python3
"""Reproduce the article's optional decimal tables. Not a certificate."""
from __future__ import annotations
import json
from pathlib import Path
import mpmath as mp
from diagnostics import integral_F
from numeric_em import F_all


def main() -> None:
    mp.mp.dps = 35
    samples = [{"rho":"0", "a_minus":"1"}]
    a = mp.mpf(1)
    for rs in ('.1','.3','.5','.7','.9','.99'):
        rho = mp.mpf(rs)
        a = mp.findroot(lambda x: integral_F(2,1,x,rho),
                        (a-mp.mpf('.02'),a+mp.mpf('.02')), tol=mp.mpf('1e-27'))
        if not 0 < a < mp.mpf('1.3'):
            raise ArithmeticError("Root solver left the proved lower-branch interval.")
        samples.append({"rho":str(rho),"a_minus":str(a)})
    guesses = {1:('1.13789','1.63894','2.12490'),
               2:('1.37133','1.91136','148.9122'),
               3:('.94095','1.12929','1.63578','6.13613','319.6184')}
    fifth = {}
    for k, initial in guesses.items():
        roots = [mp.findroot(lambda x: F_all(k,x,5,N=40,M=20)[5], mp.mpf(g),
                             tol=mp.mpf('1e-27')) for g in initial]
        fifth[str(k)] = {"roots":[str(x) for x in roots]}
        if k>1:
            fifth[str(k)]["predecessor_values"] = [
                str(F_all(k-1,x,5,N=40,M=20)[5]) for x in roots]
    data = {"status":"numerical diagnostics only; not interval certificates",
            "dps":mp.mp.dps,"n2_lower_branch":samples,"n5_classical":fifth}
    out=Path(__file__).resolve().parents[1]/'certificates'/'branch_samples.json'
    out.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__': main()
