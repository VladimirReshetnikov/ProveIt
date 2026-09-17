#!/usr/bin/env python3
"""Exact, basis-independent BCH and Zassenhaus computations.

Python >=3.10; standard library only. Noncommutative polynomials are sparse
word -> Fraction dictionaries. All calculations are in Q<X,Y>/(degree>N).
This is finite-degree verification, not a replacement for the paper's proofs.
Run: python3 code/verify_bch.py --degree 10 --out data
"""
from __future__ import annotations
import argparse
import json
import math
import time
from collections import defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from pathlib import Path
from typing import Iterable

Poly = dict[str, Q]
ONE: Poly = {'': Q(1)}
X: Poly = {'X': Q(1)}
Y: Poly = {'Y': Q(1)}


def add(*polys: Poly) -> Poly:
    out: dict[str, Q] = defaultdict(Q)
    for p in polys:
        for w, c in p.items():
            out[w] += c
    return {w: c for w, c in out.items() if c}


def scale(p: Poly, c: Q | int) -> Poly:
    return {w: c * v for w, v in p.items() if c * v}


def mul(p: Poly, q: Poly, N: int) -> Poly:
    out: dict[str, Q] = defaultdict(Q)
    for u, a in p.items():
        for v, b in q.items():
            if len(u) + len(v) <= N:
                out[u + v] += a * b
    return {w: c for w, c in out.items() if c}


def comm(p: Poly, q: Poly, N: int) -> Poly:
    return add(mul(p, q, N), scale(mul(q, p, N), -1))


def homogeneous(p: Poly, n: int) -> Poly:
    return {w: c for w, c in p.items() if len(w) == n}


def exp(p: Poly, N: int) -> Poly:
    if p.get('', 0):
        raise ValueError('Formal exponential requires zero constant term.')
    ans, power = dict(ONE), dict(ONE)
    for k in range(1, N + 1):
        power = scale(mul(power, p, N), Q(1, k))
        if not power:
            break
        ans = add(ans, power)
    return ans


def log(p: Poly, N: int) -> Poly:
    if p.get('', 0) != 1:
        raise ValueError('Formal logarithm requires constant term one.')
    q = add(p, scale(ONE, -1))
    ans, power = {}, dict(ONE)
    for k in range(1, N + 1):
        power = mul(power, q, N)
        if not power:
            break
        ans = add(ans, scale(power, Q((-1)**(k+1), k)))
    return ans


@lru_cache(maxsize=None)
def right_bracket(w: str) -> Poly:
    if not w:
        return {}
    if len(w) == 1:
        return {w: Q(1)}
    return comm({w[0]: Q(1)}, right_bracket(w[1:]), len(w))


def dynkin_project(p: Poly) -> Poly:
    ans: Poly = {}
    for w, c in p.items():
        if w:
            ans = add(ans, scale(right_bracket(w), c / len(w)))
    return ans


def ad_word(w: str, p: Poly, N: int) -> Poly:
    for a in reversed(w):
        p = comm({a: Q(1)}, p, N)
    return p


def bch_word(N: int) -> Poly:
    return log(mul(exp(X, N), exp(Y, N), N), N)


def poincare(N: int) -> Poly:
    """Independent all-orders operator-block formula from the paper."""
    q = add(mul(exp(X, N-1), exp(Y, N-1), N-1), scale(ONE, -1))
    power = dict(ONE)
    operators: dict[str, Q] = defaultdict(Q)
    # Combine equal operator words before expanding nested commutators.
    # This avoids expanding the same word once for every logarithm power.
    for k in range(1, N):
        power = mul(power, q, N-1)
        factor = Q((-1)**(k+1), k*(k+1))
        for w, c in power.items():
            operators[w] += factor * c
    ans: dict[str, Q] = defaultdict(Q, add(X, Y))
    for w, c in operators.items():
        if c:
            c /= 1 + w.count('Y')
            for v, a in ad_word(w, Y, N).items():
                ans[v] += c * a
    return {w: c for w, c in ans.items() if c}


def bernoulli_coeffs(N: int, plus: bool = True) -> list[Q]:
    """Coefficients of z/(1-exp(-z)) or z/(exp(z)-1), NOT B_n."""
    a = [Q(((-1)**j if plus else 1), math.factorial(j+1)) for j in range(N+1)]
    h = [Q(1)]
    for n in range(1, N+1):
        h.append(-sum((a[j]*h[n-j] for j in range(1,n+1)), Q(0)))
    return h


def derivative_bch(N: int) -> Poly:
    """Total-degree Bernoulli recursion using the right log derivative."""
    b = bernoulli_coeffs(N, plus=False)
    R = dict(X)
    p = dict(Y)
    for j in range(N):
        R = add(R, scale(p, Q(1, math.factorial(j))))
        p = comm(X, p, N)
    Z: Poly = {}
    for n in range(1, N+1):
        rhs, a = {}, R
        for k in range(n):
            rhs = add(rhs, scale(a, b[k]))
            a = comm(Z, a, n)
        Z = add(Z, scale(homogeneous(rhs,n), Q(1,n)))
    return Z


def displayed_bch6() -> Poly:
    R = right_bracket
    return add(X,Y,scale(R('XY'),Q(1,2)),
        scale(add(R('XXY'),R('YYX')),Q(1,12)),
        scale(R('YXXY'),Q(-1,24)),
        scale(add(R('YYYYX'),R('XXXXY')),Q(-1,720)),
        scale(add(R('XYYYX'),R('YXXXY')),Q(1,360)),
        scale(add(R('YXYXY'),R('XYXYX')),Q(1,120)),
        scale(R('XYXYXY'),Q(1,240)),
        scale(add(R('XYXXXY'),scale(R('XXYYXY'),-1)),Q(1,720)),
        scale(add(R('XYYYXY'),scale(R('XXYXXY'),-1)),Q(1,1440)))


def zassenhaus(N: int) -> dict[int,Poly]:
    R = mul(mul(exp(scale(Y,-1),N),exp(scale(X,-1),N),N),exp(add(X,Y),N),N)
    Cs: dict[int,Poly] = {}
    for n in range(2,N+1):
        Cs[n] = homogeneous(R,n)
        R = mul(exp(scale(Cs[n],-1),N),R,N)
        assert all(not w or len(w)>n for w in R), 'Residual order failed'
    assert R == ONE
    return Cs


def zassenhaus_differential(N: int) -> dict[int,Poly]:
    # The coefficient of t^k is homogeneous of word degree k+1.
    F: Poly = {}
    for k in range(1,N):
        for j in range(1,k+1):
            F = add(F,scale(ad_word('Y'*(k-j)+'X'*j,Y,N),
                            Q((-1)**k,math.factorial(j)*math.factorial(k-j))))
    out = {}
    for n in range(2,N+1):
        C = scale(homogeneous(F,n),Q(1,n))
        out[n] = C
        F = add(F,scale(C,-n))
        base, corr = F, dict(F)
        # t^n is implicit in the word degree of C.
        for j in range(1,N//n+1):
            base = comm(C,base,N)
            corr = add(corr,scale(base,Q((-1)**j,math.factorial(j))))
        F = corr
    return out


def weighted_partitions(n: int, minimum: int=2, maximum: int|None=None):
    """Nondecreasing integer tuples with sum n."""
    if n == 0:
        yield ()
        return
    upper = min(n,maximum if maximum is not None else n)
    for j in range(minimum,upper+1):
        for tail in weighted_partitions(n-j,j,upper):
            yield (j,)+tail


def forest_polynomials(N: int) -> dict[int,dict[tuple[int,...],Q]]:
    """Unrolled tree formula, with each leaf R_d represented by integer d."""
    Cs: dict[int,dict[tuple[int,...],Q]]={}
    for n in range(2,N+1):
        out: dict[tuple[int,...],Q]=defaultdict(Q)
        out[(n,)]=Q(1)
        for parts in weighted_partitions(n,maximum=n-1):
            if len(parts)<2:
                continue
            multiplicities = {j:parts.count(j) for j in set(parts)}
            coeff = -Q(1,math.prod(math.factorial(v) for v in multiplicities.values()))
            p = {():coeff}
            for j in parts:
                nxt: dict[tuple[int,...],Q]=defaultdict(Q)
                for a,c in p.items():
                    for b,d in Cs[j].items():
                        nxt[a+b]+=c*d
                p=dict(nxt)
            for w,c in p.items(): out[w]+=c
        Cs[n]={w:c for w,c in out.items() if c}
    return Cs


def verify_tree(N: int, Cs: dict[int,Poly]) -> dict:
    R = mul(mul(exp(scale(Y,-1),N),exp(scale(X,-1),N),N),exp(add(X,Y),N),N)
    Rs={n:homogeneous(R,n) for n in range(2,N+1)}
    tree=forest_polynomials(N)
    for n, formula in tree.items():
        p: Poly={}
        for leaves,c in formula.items():
            mon=dict(ONE)
            for j in leaves: mon=mul(mon,Rs[j],n)
            p=add(p,scale(mon,c))
        assert p==Cs[n],f'Tree formula failed at n={n}'
    return {str(n):{' '.join(map(str,w)):str(c) for w,c in p.items()} for n,p in tree.items()}


def coproduct_primitive(p: Poly) -> bool:
    out: dict[tuple[str,str],Q]=defaultdict(Q)
    for w,c in p.items():
        n=len(w)
        for mask in range(1,(1<<n)-1):
            u=''.join(w[j] for j in range(n) if mask>>j&1)
            v=''.join(w[j] for j in range(n) if not mask>>j&1)
            out[(u,v)]+=c
    return all(c==0 for c in out.values())


def duhamel(N: int) -> Poly:
    ans=dict(ONE)
    def compositions(total: int,k: int):
        if k==1:
            yield (total,)
        else:
            for j in range(total+1):
                for tail in compositions(total-j,k-1): yield (j,)+tail
    for k in range(1,N+1):
        for total in range(N-k+1):
            for ns in compositions(total,k):
                den=math.prod(math.factorial(j) for j in ns)
                den*=math.prod(sum(ns[j:])+k-j for j in range(k))
                p=dict(ONE)
                for j in ns: p=mul(p,ad_word('X'*j,Y,N),N)
                ans=add(ans,scale(p,Q((-1)**total,den)))
    return mul(exp(X,N),ans,N)


def serialize(p: Poly) -> dict[str,str]:
    return {w:str(p[w]) for w in sorted(p,key=lambda w:(len(w),w))}


def run(N: int,out: Path) -> None:
    start=time.perf_counter(); tests=[]
    def check(name: str, condition: bool):
        if not condition: raise AssertionError(name)
        tests.append(name)
        print(f"PASS  {name}", flush=True)
    Z=bch_word(N)
    check('exp(BCH)=exp(X)exp(Y)',exp(Z,N)==mul(exp(X,N),exp(Y,N),N))
    check('Dynkin-Specht-Wever projection',dynkin_project(Z)==Z)
    check('Poincare all-orders operator-block formula',poincare(N)==Z)
    check('Bernoulli differential recursion',derivative_bch(N)==Z)
    check('Complete displayed BCH polynomial through degree six',
          {w:c for w,c in Z.items() if len(w)<=6}==displayed_bch6())
    swap={w.translate(str.maketrans('XY','YX')):c for w,c in Z.items()}
    check('Exchange parity symmetry',swap=={w:(-1)**(len(w)+1)*c for w,c in Z.items()})
    check('Primitive coproduct through min(N,10)',coproduct_primitive({w:c for w,c in Z.items() if len(w)<=10}))
    h=bernoulli_coeffs(N)
    single={w:c for w,c in Z.items() if w.count('Y')==1}
    expected={}
    for k in range(N): expected=add(expected,scale(ad_word('X'*k,Y,N),h[k]))
    check('All single-Y coefficients',single==expected)
    Cs=zassenhaus(N)
    check('Two independent Zassenhaus recursions',Cs==zassenhaus_differential(N))
    reconstructed=mul(exp(X,N),exp(Y,N),N)
    for C in Cs.values(): reconstructed=mul(reconstructed,exp(C,N),N)
    check('Zassenhaus ordered product',reconstructed==exp(add(X,Y),N))
    for n,C in Cs.items(): check(f'Zassenhaus C_{n} is a Lie polynomial',dynkin_project(C)==C)
    tree=verify_tree(N,Cs)
    check('Nonrecursive rooted-tree formula for all C_n',True)
    check('Displayed Zassenhaus C_2',Cs[2]==scale(right_bracket('XY'),Q(-1,2)))
    check('Displayed Zassenhaus C_3',Cs[3]==add(scale(right_bracket('XXY'),Q(1,6)),scale(right_bracket('YXY'),Q(1,3))))
    check('Displayed Zassenhaus C_4',Cs[4]==add(scale(right_bracket('XXXY'),Q(-1,24)),scale(right_bracket('YXXY'),Q(-1,8)),scale(right_bracket('YYXY'),Q(-1,8))))
    M=min(N,10)
    check('Ordered-simplex Duhamel all-terms expansion through min(N,10)',duhamel(M)==exp(add(X,Y),M))
    symmetric=log(mul(mul(exp(scale(X,Q(1,2)),N),exp(Y,N),N),exp(scale(X,Q(1,2)),N),N),N)
    check('Symmetric BCH has only odd degree',all(len(w)%2 for w in symmetric))
    check('Symmetric BCH degree three',homogeneous(symmetric,3)==add(scale(right_bracket('XXY'),Q(-1,24)),scale(right_bracket('YXY'),Q(-1,12))))
    out.mkdir(parents=True,exist_ok=True)
    (out/'bch_words.json').write_text(json.dumps({'degree':N,'coefficients':serialize(Z)},indent=2)+'\n')
    (out/'zassenhaus_words.json').write_text(json.dumps({str(n):serialize(C) for n,C in Cs.items()},indent=2)+'\n')
    (out/'zassenhaus_tree_polynomials.json').write_text(json.dumps(tree,indent=2)+'\n')
    (out/'symmetric_bch_words.json').write_text(json.dumps({'degree':N,'coefficients':serialize(symmetric)},indent=2)+'\n')
    report={'degree':N,'checks_passed':len(tests),'checks':tests,
            'elapsed_seconds':round(time.perf_counter()-start,3),
            'bch_word_counts':{str(n):len(homogeneous(Z,n)) for n in range(1,N+1)},
            'zassenhaus_word_counts':{str(n):len(C) for n,C in Cs.items()},
            'arithmetic':'fractions.Fraction (exact rational arithmetic)',
            'limitations':'Finite-degree symbolic checks; no proof-assistant certification. No numerical tests of unbounded operators.'}
    (out/'verification_results.json').write_text(json.dumps(report,indent=2)+'\n')
    (out/'verification_report.txt').write_text('\n'.join([f'EXACT VERIFICATION THROUGH DEGREE {N}',f'{len(tests)} checks passed',*['PASS  '+s for s in tests],f"Elapsed: {report['elapsed_seconds']} seconds",report['limitations']])+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree',type=int,default=10)
    parser.add_argument('--out',type=Path,default=Path('data'))
    args=parser.parse_args()
    if not 6<=args.degree<=14: parser.error('--degree must be between 6 and 14; complexity grows exponentially.')
    run(args.degree,args.out)
