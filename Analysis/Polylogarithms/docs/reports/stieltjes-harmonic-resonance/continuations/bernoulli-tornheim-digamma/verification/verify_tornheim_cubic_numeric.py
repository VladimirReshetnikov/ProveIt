"""Independent Mellin numerical diagnostic of an exact third-derivative identity.

The evaluator uses integrated Jonquiere series below x=1 and the
incomplete-Gamma sum above x=1. It does not use the proposed third-jet
formula, the digamma moment, or any fitted primitive cubic constants.
Truncation and rounding are not enclosed by interval arithmetic; this
is a diagnostic accompanying the analytic proof.
"""
import argparse
import json
import time
from pathlib import Path

import mpmath as mp


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--dps",type=int,default=50)
    parser.add_argument("--terms",type=int,default=48)
    parser.add_argument("--tail",type=int,default=110)
    parser.add_argument("--steps",type=int,default=7)
    parser.add_argument("--h",default="0.0008")
    args=parser.parse_args()
    mp.mp.dps=args.dps
    K,N=args.terms,args.tail
    facts=[mp.factorial(k) for k in range(K+1)]
    logs=[mp.log(k) for k in range(1,N)]
    start=time.monotonic()

    def tornheim(a,b,c):
        ga,gb=mp.gamma(1-a),mp.gamma(1-b)
        za=[(-1)**k*mp.zeta(a-k)/facts[k] for k in range(K+1)]
        zb=[(-1)**k*mp.zeta(b-k)/facts[k] for k in range(K+1)]
        terms=[ga*gb/(a+b+c-2)]
        terms.extend(ga*zb[k]/(a+c-1+k) for k in range(K+1))
        terms.extend(gb*za[k]/(b+c-1+k) for k in range(K+1))
        terms.extend(za[j]*zb[k]/(c+j+k) for j in range(K+1)
                     for k in range(K+1))
        small=mp.fsum(terms)
        head=[mp.exp(-a*u) for u in logs]
        other=[mp.exp(-b*u) for u in logs]
        large=mp.fsum(mp.gammainc(c,k,mp.inf)/mp.power(k,c)
                     *mp.fsum(head[j-1]*other[k-j-1] for j in range(1,k))
                     for k in range(2,N+1))
        return (small+large)/mp.gamma(c)

    def interpolate_zero(xs,ys):
        return mp.fsum(y*mp.fprod(-xj/(xi-xj)
                                 for j,xj in enumerate(xs) if j!=i)
                       for i,(xi,y) in enumerate(zip(xs,ys)))

    rows=[]
    third_values=[]
    for weights,ray in [(1,(1,2,3)),(4,(2,3,1)),(-5,(3,1,2))]:
        hs=[mp.mpf(args.h)/2**j for j in range(args.steps)]
        odd=[]
        for j,h in enumerate(hs):
            plus=tornheim(*(h*x for x in ray))
            minus=tornheim(*(-h*x for x in ray))
            odd.append((plus-minus)/(2*h))
            print(json.dumps({"ray":ray,"step":j+1,
                              "elapsed_seconds":round(time.monotonic()-start,2)}),flush=True)
        xs=[h*h for h in hs[:-1]]
        approximations=[6*(odd[j]-odd[j+1])/(hs[j]**2-hs[j+1]**2)
                        for j in range(args.steps-1)]
        third=interpolate_zero(xs,approximations)
        previous=interpolate_zero(xs[:-1],approximations[:-1])
        third_values.append(third)
        row={"ray":ray,"weight":weights,"third_derivative":mp.nstr(third,42),
             "last_extrapolation_change":mp.nstr(abs(third-previous),8)}
        rows.append(row)
        print(json.dumps(row),flush=True)
    lhs=third_values[0]+4*third_values[1]-5*third_values[2]
    rhs=(99*mp.zeta(0,derivative=1)*mp.zeta(0,derivative=2)
         +mp.mpf(207)/2*mp.zeta(0,derivative=3)
         +mp.mpf(162)/5*mp.zeta(-1,derivative=3))
    error=abs(lhs-rhs)
    output={"method":"Jonquiere--Mellin sum and incomplete-Gamma tail; odd-part extrapolation",
            "qualification":"Non-interval numerical diagnostic, not used as proof",
            "working_dps":args.dps,"jonquiere_index":K,"tail_index":N,
            "steps":args.steps,"initial_h":args.h,"records":rows,
            "combination_numeric":mp.nstr(lhs,42),"combination_exact_formula":mp.nstr(rhs,42),
            "absolute_error":mp.nstr(error,10),
            "elapsed_seconds":round(time.monotonic()-start,2),
            "status":"PASS" if error<mp.mpf("1e-23") else "CHECK"}
    destination=Path(__file__).resolve().parent.parent / "results" / "tornheim_cubic_numeric.json"
    destination.write_text(json.dumps(output,indent=2)+"\n")
    print(json.dumps(output,indent=2),flush=True)
    assert error<mp.mpf("1e-23")


if __name__=="__main__":
    main()
