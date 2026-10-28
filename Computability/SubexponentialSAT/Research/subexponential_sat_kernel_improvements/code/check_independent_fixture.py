#!/usr/bin/env python3
"""Independent exact-rational crossing-kernel fixture for the Smith separator.

Q[omega]/(omega^2+omega+1) arithmetic below is independent of the modular
Ring implementation, including inversion and full Cauchy-kernel preparation.
"""
from fractions import Fraction as F
import itertools
import json
import argparse
from math import prod
from pathlib import Path

from adaptive_modes import Ring, separate, crossing_kernel


def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def mul(x,y):
    a,b=x;c,d=y
    return (a*c-b*d,a*d+b*c-b*d)
def inverse(x):
    a,b=x
    norm=a*a-a*b+b*b
    if norm == 0: raise ZeroDivisionError
    return ((a-b)/norm,-b/norm)
def quotient(x,y): return mul(x,inverse(y))
def valuation(x):
    values=[]
    for a in x:
        if a:
            num,den=abs(a.numerator),a.denominator
            values.append((num & -num).bit_length()-(den & -den).bit_length())
    return min(values) if values else 10**9
def det(matrix):
    out=(F(0),F(0));n=len(matrix)
    for perm in itertools.permutations(range(n)):
        term=(F(1),F(0))
        for i,j in enumerate(perm): term=mul(term,matrix[i][j])
        inv=sum(perm[i]>perm[j] for i in range(n) for j in range(i+1,n))
        out=add(out,neg(term) if inv%2 else term)
    return out
def require(condition,message):
    if not condition: raise RuntimeError(message)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output",type=Path,
        default=Path(__file__).resolve().parents[1]/"results/local_checks/independent_fixture_result.json")
    args=parser.parse_args()
    a,t,p=4,1,64
    L=1<<a
    rows=(0,4,12);columns=(0,8,12)
    T=(F(t),F(2*L))
    C=(F(1),F(0))
    for v in range(-L,L): C=mul(C,add(T,(F(-v),F(0))))
    derivative=prod(-v for v in range(-L,L) if v)
    gamma=(C[0]/derivative,C[1]/derivative)
    exact=[[quotient(gamma,add(T,(F(x-y),F(0)))) for y in columns] for x in rows]
    modulus=1<<p
    def reduce(x):
        require(all(c.denominator%2 for c in x),"nonintegral exact kernel coordinate")
        return tuple((c.numerator*pow(c.denominator,-1,modulus))%modulus for c in x)
    oracle=[[reduce(x) for x in row] for row in exact]
    ring=Ring(p,(1,1,1))
    require(crossing_kernel(a,t,(0,1),rows,columns,ring)==oracle,
            "modular kernel differs from exact rational kernel")
    modes=separate(oracle,ring)
    # Reconstruct with the independent pair multiplication above, then reduce.
    reconstructed=[]
    for i in range(len(rows)):
        out=[]
        for j in range(len(columns)):
            value=(F(0),F(0))
            for mode in modes: value=add(value,mul(mode.target[i],mode.source[j]))
            out.append(reduce(value))
        reconstructed.append(out)
    require(reconstructed==oracle,"independent reconstruction failed")
    determinantal=[]
    for k in range(1,4):
        determinantal.append(min(valuation(det([[exact[i][j] for j in J] for i in I]))
            for I in itertools.combinations(range(3),k)
            for J in itertools.combinations(range(3),k)))
    weights=[m.weight for m in modes]
    require([sum(weights[:k]) for k in range(1,4)]==determinantal,
            "exact determinantal valuations differ from Smith weights")
    result={"status":"passed","L":L,"t":t,"precision":p,
            "zeta":"omega, with omega^2+omega+1=0",
            "rows":rows,"columns":columns,"smith_weights":weights,
            "exact_determinantal_valuations":determinantal,
            "oracle":"full rational Cauchy kernel over Q[omega], independent arithmetic"}
    path=args.output
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(result,indent=2)+"\n")
    print(json.dumps(result))


if __name__ == "__main__": main()
