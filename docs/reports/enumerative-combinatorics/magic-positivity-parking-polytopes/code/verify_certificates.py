#!/usr/bin/env python3
"""Verify stored exact certificates and run independent geometric checks.

Python 3.9+ standard library only.  Default checks include full regeneration.
Use --skip-regeneration to audit stored coefficients and independent identities.
No floating-point arithmetic is used in any mathematical check.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import product
from math import comb, factorial
from pathlib import Path
import json
import time

from sparse_magic import (evaluate, kernel, magic_polynomials, next_lattice,
                         read_poly, Poly)

ROOT = Path(__file__).resolve().parents[1]


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ArithmeticError(message)


def verify_kernels(max_degree: int) -> int:
    """Independently check K(X,Y,Z)-K(X+1,Y-1,Z)=D X^a(Z+Y)^b."""
    D = factorial(max_degree + 1)
    count = 0
    for a in range(max_degree + 1):
        for b in range(max_degree + 1 - a):
            K = dict(kernel(a, b, D))
            require(all(e[1] > 0 for e in K), 'Kernel boundary K(X,0,Z) is nonzero')
            difference = defaultdict(int, K)
            for (u,v,w),c in K.items():
                for i in range(u+1):
                    for j in range(v+1):
                        difference[(i,j,w)] -= c*comb(u,i)*comb(v,j)*(-1)**(v-j)
            actual = {e:c for e,c in difference.items() if c}
            expected = {(a,j,b-j):D*comb(b,j) for j in range(b+1)}
            require(actual == expected, f'Kernel identity failed at {(a,b)}')
            count += 1
    return count


def geometric_count(b: tuple[int, ...], t: int) -> int:
    """Count lattice points using sorted tuples and subset inequalities only.

    This does not use lattice slicing, Faulhaber sums, or Ehrhart interpolation.
    A decreasing tuple represents n!/prod(multiplicity!) coordinate permutations.
    """
    if not b or any(v < 1 for v in b) or t < 0:
        raise ValueError('Positive parameters and nonnegative dilation required')
    n = len(b)
    partial, s = [], 0
    for v in b:
        s += v
        partial.append(t*(s-1))
    caps, s = [], 0
    for v in reversed(partial):
        s += v
        caps.append(s)
    total, nfac = 0, factorial(n)
    values = []
    def visit(i: int, upper: int, used: int) -> None:
        nonlocal total
        if i == n:
            orbit = nfac
            for m in Counter(values).values():
                orbit //= factorial(m)
            total += orbit
            return
        for v in range(min(upper, caps[i]-used)+1):
            values.append(v)
            visit(i+1, v, used+v)
            values.pop()
    visit(0, caps[0], 0)
    return total


def first_magic(n: int) -> dict[tuple[int,...], Fraction]:
    H = [Fraction(0)]
    for i in range(1,n+1):
        H.append(H[-1]+Fraction(1,i))
    result = {(0,)*n:Fraction(n*(3*n-7),4)}
    for j in range(n):
        e = tuple(int(i==j) for i in range(n))
        r = n-j
        result[e] = Fraction(n) if j==0 else r*(1+H[n]-H[r])
    return {e:c for e,c in result.items() if c}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--certificates',type=Path,default=ROOT/'data'/'certificates')
    parser.add_argument('--output',type=Path,default=ROOT/'data'/'verification.json')
    parser.add_argument('--skip-regeneration',action='store_true')
    args = parser.parse_args()
    began = time.monotonic()
    records = []
    prev = {(1,):1}
    count_coefficients = 0
    stored = {}
    for n in range(1,11):
        P = read_poly(args.certificates/f'lattice_{n:02d}.json')
        M = [read_poly(args.certificates/f'magic_{n:02d}_{j:02d}.json') for j in range(n+1)]
        for e,c in P.items():
            require(len(e)==n and sum(e)<=n and isinstance(c,int), 'Bad lattice record')
        if not args.skip_regeneration:
            if n>1:
                prev = next_lattice(prev,n)
            require(P==prev,f'Lattice regeneration failed: n={n}')
            require(M==magic_polynomials(P,n),f'Magic regeneration failed: n={n}')
        require(M[0]=={(0,)*n:factorial(n)},f'Constant magic coefficient failed: {n}')
        expected_first = {e:int(c*factorial(n)) for e,c in first_magic(n).items()}
        require(M[1]==expected_first,f'First-coefficient formula failed: {n}')
        if n>=3:
            for j,pol in enumerate(M):
                require(all(c>0 for c in pol.values()),f'Negative coefficient: n={n},j={j}')
                require(all(sum(e)<=j for e in pol),f'Degree bound: n={n},j={j}')
                expected_terms = comb(n+j,j)-(1 if (n,j)==(3,3) else 0)
                require(len(pol)==expected_terms,f'Support size: n={n},j={j}')
                count_coefficients += len(pol)
        stored[n]=(P,M)
        records.append({'dimension':n,'lattice_terms':len(P),
                        'magic_terms':[len(p) for p in M],
                        'negative_magic_terms':[sum(c<0 for c in p.values()) for p in M]})
        print(f'Certificate n={n}: passed',flush=True)
    kernels = verify_kernels(9)
    print(f'{kernels} independent kernel identities: passed',flush=True)
    cases = []
    for n,base,ts in [(3,4,range(4)),(4,3,range(3)),(5,2,range(3)),(6,2,range(2))]:
        for b in product(range(1,base+1),repeat=n):
            for t in ts:
                cases.append((b,t))
    for n in range(7,11):
        for t in (0,1):
            cases.append(((1,)*n,t))
    checked = []
    for b,t in cases:
        n=len(b)
        P,M=stored[n]
        geometric=geometric_count(b,t)
        dilated=(1+t*(b[0]-1),)+tuple(t*v for v in b[1:])
        x=tuple(v-1 for v in b)
        via_lattice=evaluate(P,dilated)
        via_magic=sum(evaluate(p,x)*t**j*(t+1)**(n-j) for j,p in enumerate(M))
        require(via_lattice==factorial(n)*geometric, f'Geometry vs lattice: {b},t={t}')
        require(via_magic==via_lattice,f'Geometry vs magic: {b},t={t}')
        checked.append({'b':list(b),'t':t,'count':geometric})
    print(f'{len(checked)} independent geometric counts: passed',flush=True)
    # Explicit example printed in the source paper, not used to build certificates.
    _,M=stored[3]
    example=[Fraction(evaluate(p,(1,2,0)),6) for p in M]
    require(example==[Fraction(1),Fraction(59,6),Fraction(115,3),Fraction(54)],'Source example')
    report={'status':'PASS','exact_arithmetic':True,
            'full_regeneration':not args.skip_regeneration,
            'positive_scaled_coefficients_n3_to_n10':count_coefficients,
            'kernel_identity_count':kernels,'geometric_case_count':len(checked),
            'certificates':records,'source_example_2_3_1':[str(x) for x in example],
            'geometric_checks':checked,'elapsed_seconds':round(time.monotonic()-began,3)}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(f'ALL CHECKS PASSED in {report["elapsed_seconds"]} seconds',flush=True)

if __name__=='__main__':
    main()
