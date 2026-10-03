#!/usr/bin/env python3
"""Exact finite audits for 'Exact Type Beyond Log-Convexity'.

No network access or third-party packages.  The computations test finite
identities and bounds; the asymptotic theorems are proved in article.tex.
Default outputs go to build/verification, leaving the recorded data untouched.
"""
from __future__ import annotations
import argparse
import csv
import json
import math
import platform
import random
from fractions import Fraction as Q
from pathlib import Path
from typing import Iterator


def partitions(n: int, minimum: int = 1) -> Iterator[tuple[int, ...]]:
    if n == 0:
        yield ()
    else:
        for j in range(minimum, n + 1):
            for tail in partitions(n-j, j):
                yield (j,) + tail


def envelope(weights: list[Q]) -> tuple[list[Q], list[tuple[int, ...]]]:
    """Max-product dynamic program, with a maximizing partition witness."""
    if not weights or weights[0] != 1 or any(x <= 0 for x in weights):
        raise ValueError('Positive weights with weights[0] = 1 are required.')
    s, witnesses = [Q(1)], [()]
    for n in range(1, len(weights)):
        candidates = [(weights[j]*s[n-j], (j,)+witnesses[n-j])
                      for j in range(1, n+1)]
        value, witness = max(candidates, key=lambda pair: pair[0])
        s.append(value)
        witnesses.append(witness)
    return s, witnesses


def mul(a: list[Q], b: list[Q], degree: int) -> list[Q]:
    out = [Q(0)]*(degree+1)
    for i, ai in enumerate(a[:degree+1]):
        if ai:
            for j, bj in enumerate(b[:degree-i+1]):
                if bj:
                    out[i+j] += ai*bj
    return out


def compose(a: list[Q], b: list[Q], degree: int) -> list[Q]:
    if b[0] != 0:
        raise ValueError('The inner constant coefficient must vanish.')
    out = [Q(0)]*(degree+1)
    power = [Q(1)]+[Q(0)]*degree
    for k, ak in enumerate(a[:degree+1]):
        if ak:
            for j in range(degree+1):
                out[j] += ak*power[j]
        if k < degree:
            power = mul(power, b, degree)
    return out


def inverse_lagrange(a: list[Q]) -> list[Q]:
    """Inverse of z + sum a[n+1] z**(n+1), by precomputed powers."""
    if len(a) < 2 or a[0] != 0 or a[1] != 1:
        raise ValueError('A tangent-to-identity series is required.')
    degree = len(a)-1
    A = [Q(0)] + a[2:]
    powers = [[Q(1)]+[Q(0)]*(degree-1)]
    for k in range(1, degree):
        powers.append(mul(powers[-1], A, degree-1))
    g = [Q(0), Q(1)]+[Q(0)]*(degree-1)
    for n in range(1, degree):
        g[n+1] = sum((Q((-1)**k*math.comb(n+k,k), n+1)*powers[k][n]
                      for k in range(1,n+1)), Q(0))
    return g


def inverse_picard(a: list[Q]) -> list[Q]:
    degree = len(a)-1
    ident = [Q(0),Q(1)]+[Q(0)]*(degree-1)
    p = a.copy()
    p[1] = Q(0)
    g = ident.copy()
    for _ in range(degree-1):
        pg = compose(p,g,degree)
        g = [ident[j]-pg[j] for j in range(degree+1)]
    return g


def positive_inverse(weights: list[Q], amplitude: Q = Q(1)) -> list[Q]:
    return inverse_lagrange([Q(0), Q(1)] + [-amplitude*x for x in weights[1:]])


def partition_inverse_coefficient(weights: list[Q], n: int, c: Q) -> Q:
    answer = Q(0)
    for part in partitions(n):
        mult: dict[int,int] = {}
        prod = Q(1)
        for j in part:
            mult[j] = mult.get(j,0)+1
            prod *= weights[j]
        k = len(part)
        den = math.factorial(n+1)
        for multiplicity in mult.values():
            den *= math.factorial(multiplicity)
        factor = Q(math.factorial(n+k),den)
        assert factor.denominator == 1
        answer += factor*c**k*prod
    return answer


def count(n: int, k: int) -> Q:
    return Q(math.comb(n+k,k)*math.comb(n-1,k-1), n+1)


def ceil_root(q: Q, n: int) -> int:
    """Least nonnegative integer b with b**n >= q, using exact comparisons."""
    if q <= 1:
        return 1
    low, high = 0, 1 << ((q.numerator.bit_length()+n-1)//n)
    while low+1 < high:
        mid = (low+high)//2
        if mid**n*q.denominator >= q.numerator:
            high=mid
        else:
            low=mid
    return high


def finite_split_bound(w: list[Q], s: list[Q], n: int, c: Q, eta: Q) -> Q:
    L = math.ceil(2/eta)
    B = max([1] + [ceil_root(w[j],j) for j in range(1,min(L,n)+1)])
    ell0 = math.ceil(eta*n/2)
    tail = max(Q(B)**ell/s[ell] for ell in range(ell0,n+1))
    sparse = sum((count(n,k)*c**k for k in range(1,n+1) if k <= eta*n),Q(0))
    dense = sum((count(n,k)*c**k for k in range(1,n+1) if k > eta*n),Q(0))
    return s[n]*(sparse+dense*tail)


def weight_family(name: str, degree: int) -> list[Q]:
    w = [Q(1)]
    for n in range(1,degree+1):
        if name == 'factorial':
            value = Q(math.factorial(n+1))
        elif name == 'staircase':
            value = Q(2**(n*(n.bit_length()-1)))
        elif name == 'alternating_supermultiplicative':
            value = Q(2**(n*n+(-1)**n*n))
        elif name == 'finite_loss':
            value = Q(math.factorial(n))* (Q(2)**(-n) if n%2 else 1)
        elif name == 'deep_dips':
            value = Q(2**(n*n if n%2==0 else (n*n-1)//4))
        elif name == 'subexponential_perturbation':
            exponent = (-1)**n*math.isqrt(n)
            value = Q(math.factorial(n+1))*Q(2)**exponent
        else:
            raise ValueError(name)
        w.append(value)
    return w

# Bivariate polynomial arithmetic, independent of the scalar implementation.
Monomial = tuple[int,int]
Poly = dict[Monomial,Q]

def p_add(a: Poly,b: Poly,scale: Q=Q(1)) -> Poly:
    c=a.copy()
    for m,v in b.items():
        c[m]=c.get(m,Q(0))+scale*v
        if c[m]==0:
            del c[m]
    return c


def p_mul(a: Poly,b: Poly,degree: int) -> Poly:
    c: Poly={}
    for (i,j),v in a.items():
        for (k,l),u in b.items():
            if i+j+k+l<=degree:
                m=(i+k,j+l)
                c[m]=c.get(m,Q(0))+v*u
    return {m:v for m,v in c.items() if v}


def p_substitute(p: Poly,g: tuple[Poly,Poly],degree: int) -> Poly:
    powers=[]
    for q in g:
        row=[{(0,0):Q(1)}]
        for _ in range(degree):
            row.append(p_mul(row[-1],q,degree))
        powers.append(row)
    out: Poly={}
    for (i,j),v in p.items():
        out=p_add(out,p_mul(powers[0][i],powers[1][j],degree),v)
    return out


def vector_inverse(f: tuple[Poly,Poly],degree: int) -> tuple[Poly,Poly]:
    identity=({(1,0):Q(1)},{(0,1):Q(1)})
    p=tuple(p_add(f[i],identity[i],Q(-1)) for i in range(2))
    g=identity
    for _ in range(degree-1):
        g=tuple(p_add(identity[i],p_substitute(p[i],g,degree),Q(-1))
                for i in range(2))
    return g


def degree_norm(f: tuple[Poly,Poly],degree: int) -> Q:
    return max(sum((abs(v) for m,v in p.items() if sum(m)==degree),Q(0)) for p in f)


def log2q(x: Q) -> float:
    return math.log2(x.numerator)-math.log2(x.denominator)


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('build/verification'))
    parser.add_argument('--order',type=int,default=36)
    args=parser.parse_args()
    if not 20<=args.order<=80:
        parser.error('--order must lie between 20 and 80')
    args.output.mkdir(parents=True,exist_ok=True)
    counters: dict[str,int]={}
    def tick(key: str, amount: int=1) -> None:
        counters[key]=counters.get(key,0)+amount
    rng=random.Random(20260929)
    diagnostics=[]
    example_rows=[]
    families=['factorial','staircase','alternating_supermultiplicative',
              'deep_dips','finite_loss','subexponential_perturbation']
    for name in families:
        w=weight_family(name,args.order)
        s,witness=envelope(w)
        h=positive_inverse(w)
        for n in range(1,args.order+1):
            assert h[n+1]>=s[n]
            assert sum(witness[n])==n
            assert math.prod(w[j] for j in witness[n])==s[n]
            tick('envelope_witness_and_inverse_lower_bound')
            for j in range(1,n):
                assert s[j]*s[n-j]<=s[n]
                tick('envelope_supermultiplicativity')
            if n<=18:
                independent=max(math.prod(w[j] for j in part) for part in partitions(n))
                assert independent==s[n]
                assert partition_inverse_coefficient(w,n,Q(1))==h[n+1]
                tick('partition_enumeration_comparisons')
            for eta in (Q(1,2),Q(1,3),Q(1,4)):
                assert h[n+1]<=finite_split_bound(w,s,n,Q(1),eta)
                tick('exact_sparse_dense_bounds')
            if name in ('staircase','alternating_supermultiplicative'):
                assert s[n]==w[n]
                tick('explicit_supermultiplicative_envelopes')
            if name=='finite_loss':
                expected = w[n] if n%2==0 else max(w[n], Q(math.factorial(n-1),2))
                assert s[n]==expected
                tick('explicit_finite_loss_repair')
            if name=='deep_dips':
                expected=Q(2**(n*n if n%2==0 else (n-1)**2))
                assert s[n]==expected
                tick('explicit_dip_repair')
            diagnostics.append({'weight':name,'excess_degree':n,
                'log2_envelope_ratio_per_degree':log2q(s[n]/w[n])/n,
                'log2_inverse_ratio_per_degree':log2q(h[n+1]/w[n])/n,
                'log2_inverse_over_envelope_per_degree':log2q(h[n+1]/s[n])/n,
                'maximizing_witness_length':len(witness[n])})
            if n in (9,17,25,33):
                example_rows.append((name,n,log2q(s[n]/w[n])/n,
                                     log2q(h[n+1]/s[n])/n))
        # Both compositions test the Lagrange result without using Lagrange again.
        D=16
        f=[Q(0),Q(1)]+[-x for x in w[1:D]]
        hi=h[:D+1]
        ident=[Q(0),Q(1)]+[Q(0)]*(D-1)
        assert compose(f,hi,D)==ident and compose(hi,f,D)==ident
        assert inverse_picard(f[:13])==hi[:13]
        tick('weight_family_two_sided_and_picard_checks')
    # Small arbitrary positive weights, not assumed to be admissible.
    for _ in range(12):
        w=[Q(1)]+[Q(rng.randint(1,20),rng.randint(1,9)) for _ in range(12)]
        s,_=envelope(w)
        c=Q(rng.randint(1,5),rng.randint(1,5))
        h=positive_inverse(w,c)
        for n in range(1,13):
            assert h[n+1]>=c**len(envelope(w)[1][n])*s[n]
            assert h[n+1]<=finite_split_bound(w,s,n,c,Q(1,3))
            assert partition_inverse_coefficient(w,n,c)==h[n+1]
            tick('arbitrary_weight_finite_audits')
    # Signed inversion, scaling, and two-input composition majorants.
    w=weight_family('subexponential_perturbation',12)
    for _ in range(24):
        f=[Q(0),Q(1)]+[Q(rng.randint(-5,5),5)*x for x in w[1:]]
        g=[Q(0),Q(1)]+[Q(rng.randint(-5,5),5)*x for x in w[1:]]
        fi=inverse_lagrange(f)
        major=positive_inverse(w,Q(1))
        major2=positive_inverse(w,Q(2))
        fg=compose(f,g,13)
        ident=[Q(0),Q(1)]+[Q(0)]*12
        assert compose(f,fi,13)==ident and compose(fi,f,13)==ident
        assert fi==inverse_picard(f)
        scale=Q(3,2)
        fs=[f[j]*scale**(j-1) if j else Q(0) for j in range(14)]
        fis=inverse_lagrange(fs)
        for j in range(2,14):
            assert abs(fi[j])<=major[j]
            assert abs(fg[j])<=major2[j]
            assert fis[j]==fi[j]*scale**(j-1)
            tick('signed_coefficient_majorants_and_scaling')
        tick('signed_two_sided_inverse_cases')
    # Explicit zero-type input whose inverse has infinite type.
    w=weight_family('deep_dips',args.order)
    f=[Q(0),Q(1),Q(-1)]
    for n in range(2,args.order+1):
        root=math.isqrt(n)
        if root*root<n:
            root+=1
        f.append(-Q(2)**(n*n-n*root) if n%2==0 else Q(0))
    g=inverse_lagrange(f)
    dip_rows=[]
    for n in range(3,args.order+1,2):
        root=math.isqrt(n-1)
        if root*root<n-1:
            root+=1
        lower=(n+2)*Q(2)**((n-1)**2-(n-1)*root)
        assert g[n+1]>=lower
        tick('zero_type_to_infinite_type_lower_bounds')
        dip_rows.append({'excess_degree':n,'log2_lower_ratio_per_degree':log2q(lower/w[n])/n,
                         'log2_actual_ratio_per_degree':log2q(g[n+1]/w[n])/n})
    # Exact two-variable inverse jets and scalar norm majorants.
    identity=({(1,0):Q(1)},{(0,1):Q(1)})
    D=7
    for _ in range(8):
        components=[]
        for i in range(2):
            p=identity[i].copy()
            for degree in range(2,5):
                for j in range(degree+1):
                    v=Q(rng.randint(-2,2),7)
                    if v:
                        p[(j,degree-j)]=v
            components.append(p)
        f=tuple(components)
        g=vector_inverse(f,D)
        fg=tuple(p_substitute(p,g,D) for p in f)
        gf=tuple(p_substitute(p,f,D) for p in g)
        assert fg==identity and gf==identity
        w=weight_family('staircase',D-1)
        c=max(degree_norm(f,n+1)/w[n] for n in range(1,D))
        major=positive_inverse(w,c)
        for j in range(2,D+1):
            assert degree_norm(g,j)<=major[j]
            tick('bivariate_homogeneous_norm_bounds')
        tick('bivariate_two_sided_inverse_cases')
    # Convexity defect at powers of two; a genuinely non-convex exact-type scale.
    convex_rows=[]
    for m in range(1,13):
        n=2**m
        ell=lambda j: j*(j.bit_length()-1)
        defect=2*ell(n)-ell(n-1)-ell(n+1)
        assert defect==n-1
        tick('staircase_convexity_defects')
        convex_rows.append({'n':n,'twice_convexity_defect_log2':defect})
    report={
        'status':'all exact finite checks passed',
        'python':platform.python_version(),'seed':20260929,'maximum_excess_degree':args.order,
        'counters':counters,
        'total_counted_checks':sum(counters.values()),
        'boundaries':[
            'No finite computation proves an asymptotic theorem.',
            'All asserted identities and inequalities use integer or rational arithmetic.',
            'Displayed logarithms are ordinary floating-point diagnostics, not interval certificates.',
            'No Lean formalization was compiled.',
            'Finite bivariate tests use maximum component coefficient-l1 norms; the Banach theorem is proved analytically.'
        ]}
    (args.output/'verification.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    for filename,rows in [('type_diagnostics.csv',diagnostics),('dip_counterexample.csv',dip_rows),
                          ('convexity_defects.csv',convex_rows)]:
        with (args.output/filename).open('w',encoding='utf-8',newline='') as file:
            writer=csv.DictWriter(file,fieldnames=list(rows[0]),lineterminator='\n')
            writer.writeheader();writer.writerows(rows)
    selected=[row for row in example_rows if row[0] in ('staircase','finite_loss','deep_dips')]
    table='\n'.join(f'{name.replace("_"," ")} & {n} & {d:.6f} & {h:.6f} \\\\'
                    for name,n,d,h in selected)
    (args.output/'diagnostic_rows.tex').write_text(table+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
