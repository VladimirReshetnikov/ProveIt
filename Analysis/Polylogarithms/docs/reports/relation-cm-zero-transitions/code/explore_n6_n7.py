"""Numerical-only evidence for proposed sixth/seventh-index zero counts.

This script does not certify a global root count or prove simplicity.
It records all scan parameters and the Euler--Maclaurin approximation.
"""
from pathlib import Path
import json
import mpmath as mp
import explore_zeros as core


def main():
    mp.mp.dps = 70
    core.ETAB[:] = [core.es(k,core.NMAX) for k in range(80)]
    results=[]
    for n in (6,7):
        points=sorted(set(
            [mp.power(10,-3+mp.mpf(j)*mp.mpf("6.1")/400)
             for j in range(401)]
            + [mp.mpf(j)/200 for j in range(60,651)]))
        values=[core.value(n,a,1,M=24,Q=16) for a in points]
        brackets=[(points[j],points[j+1]) for j in range(len(points)-1)
                  if values[j]*values[j+1]<0]
        roots=[mp.findroot(lambda a:core.value(n,a,1,M=24,Q=16),pair)
               for pair in brackets]
        row={
            "n":n,"k":1,"diagnostic_only":True,
            "working_dps":70,
            "euler_maclaurin_M":24,"euler_maclaurin_R":16,
            "scan_description":
                "401 logarithmically spaced points from 10^-3 to 10^3.1, "
                "plus 591 equally spaced points j/200, 60<=j<=650",
            "sample_points":len(points),
            "minimum_a":mp.nstr(points[0],40),
            "maximum_a":mp.nstr(points[-1],40),
            "roots":[mp.nstr(root,45) for root in roots],
            "analytic_tail_note":
                "For a>=exp(n), every summand in gamma_n_prime(a) is "
                "nonpositive and infinitely many are negative, so no "
                "positive roots can occur there."}
        results.append(row)
        print(json.dumps(row),flush=True)
    target=Path(__file__).with_name("n6_n7_conjecture_diagnostics.json")
    target.write_text(json.dumps(results,indent=2)+"\n")


if __name__=="__main__":
    main()
