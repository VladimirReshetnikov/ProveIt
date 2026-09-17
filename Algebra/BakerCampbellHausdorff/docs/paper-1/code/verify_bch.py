#!/usr/bin/env python3
"""Exact, dependency-free checks for the accompanying BCH paper.

All computations take place in Q< X,Y > modulo words above --degree.
No matrix sampling or floating-point arithmetic is used.  Word dictionaries
are intentionally transparent rather than optimized for high orders.

Run: python3 code/verify_bch.py --degree 10 --output data
"""
from __future__ import annotations
import argparse
import csv
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import factorial
from pathlib import Path
from typing import Dict, Iterable

Poly = Dict[str, Q]
ONE: Poly = {"": Q(1)}
X: Poly = {"X": Q(1)}
Y: Poly = {"Y": Q(1)}


def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for w, a in p.items():
            out[w] = out.get(w, Q(0)) + a
    return {w: a for w, a in out.items() if a}


def scale(p: Poly, a: Q | int) -> Poly:
    return {w: a * b for w, b in p.items() if a * b}


def grade(p: Poly, n: int) -> Poly:
    return {w: a for w, a in p.items() if len(w) == n}


def mul(p: Poly, q: Poly, N: int) -> Poly:
    buckets: dict[int, list[tuple[str, Q]]] = {}
    for w, a in q.items():
        buckets.setdefault(len(w), []).append((w, a))
    out: Poly = {}
    for u, a in p.items():
        for length, terms in buckets.items():
            if len(u) + length > N:
                continue
            for v, b in terms:
                w = u + v
                out[w] = out.get(w, Q(0)) + a*b
    return {w: a for w, a in out.items() if a}


def comm(p: Poly, q: Poly, N: int) -> Poly:
    return add(mul(p, q, N), scale(mul(q, p, N), -1))


def exp(p: Poly, N: int) -> Poly:
    if p.get("", 0):
        raise ValueError("Formal exponential requires zero constant term")
    out, term = ONE.copy(), ONE.copy()
    for k in range(1, N+1):
        term = scale(mul(term, p, N), Q(1, k))
        if not term:
            break
        out = add(out, term)
    return out


def log(p: Poly, N: int) -> Poly:
    if p.get("", 0) != 1:
        raise ValueError("Formal logarithm requires constant term one")
    u = add(p, scale(ONE, -1))
    out, term = {}, ONE.copy()
    for k in range(1, N+1):
        term = mul(term, u, N)
        if not term:
            break
        out = add(out, scale(term, Q((-1)**(k-1), k)))
    return out


def exp_ad(p: Poly, q: Poly, N: int) -> Poly:
    out, term = q.copy(), q.copy()
    for k in range(1, N+1):
        term = scale(comm(p, term, N), Q(1, k))
        if not term:
            break
        out = add(out, term)
    return out


@lru_cache(None)
def right_bracket(w: str) -> Poly:
    if not w:
        return {}
    if len(w) == 1:
        return {w: Q(1)}
    return comm({w[0]: Q(1)}, right_bracket(w[1:]), len(w))


def dynkin_projection(p: Poly) -> Poly:
    return add(*(scale(right_bracket(w), a / len(w))
                 for w, a in p.items() if w))


def block_weight(w: str) -> Q:
    if "YX" in w:
        return Q(0)
    return Q(1, factorial(w.count("X"))*factorial(w.count("Y")))


def cut_coefficient(w: str) -> Q:
    """Nonrecursive formula, independently enumerating all 2^(n-1) cuts."""
    n = len(w)
    if not n:
        return Q(0)
    ans = Q(0)
    for mask in range(1 << (n-1)):
        cuts = [0] + [i for i in range(1, n) if mask & (1 << (i-1))] + [n]
        k = len(cuts)-1
        term = Q((-1)**(k-1), k)
        for i, j in zip(cuts[:-1], cuts[1:]):
            term *= block_weight(w[i:j])
            if not term:
                break
        ans += term
    return ans


def bernoulli_coefficients(N: int) -> list[Q]:
    """Coefficients b_n of z/(1-exp(-z)), not B_n themselves."""
    b = [Q(1)]
    for n in range(1, N+1):
        b.append(-sum((Q((-1)**j, factorial(j+1))*b[n-j]
                       for j in range(1, n+1)), Q(0)))
    return b


def bch_recurrence(N: int) -> Poly:
    b = bernoulli_coefficients(N)
    S, T = add(X,Y), add(X,scale(Y,-1))
    Z = S.copy()
    for n in range(2, N+1):
        rhs = scale(comm(T, grade(Z,n-1), n), Q(1,2))
        term = S
        for j in range(1, n):
            term = comm(Z, term, n)
            if j % 2 == 0:
                rhs = add(rhs, scale(grade(term,n), b[j]))
        Z = add(Z, scale(rhs,Q(1,n)))
    return Z


def page_polynomial() -> Poly:
    """Exactly the page's displayed right-nested terms through degree six."""
    terms = [(1,"X"),(1,"Y"),(Q(1,2),"XY"),
        (Q(1,12),"XXY"),(Q(1,12),"YYX"),(-Q(1,24),"YXXY"),
        (-Q(1,720),"YYYYX"),(-Q(1,720),"XXXXY"),
        (Q(1,360),"XYYYX"),(Q(1,360),"YXXXY"),
        (Q(1,120),"YXYXY"),(Q(1,120),"XYXYX"),
        (Q(1,240),"XYXYXY"),
        (Q(1,720),"XYXXXY"),(-Q(1,720),"XXYYXY"),
        (Q(1,1440),"XYYYXY"),(-Q(1,1440),"XXYXXY")]
    return add(*(scale(right_bracket(w),Q(c)) for c,w in terms))


def zassenhaus_residual(N: int) -> tuple[dict[int, Poly], Poly]:
    R = mul(mul(exp(scale(Y,-1),N), exp(scale(X,-1),N),N), exp(add(X,Y),N),N)
    H = R.copy()
    C = {}
    for n in range(2,N+1):
        C[n] = grade(R,n)
        R = mul(exp(scale(C[n],-1),N), R,N)
        assert all(len(w)>n or w=="" for w in R)
    assert R == ONE
    return C,H


def zassenhaus_differential(N: int) -> dict[int, Poly]:
    F = exp_ad(scale(Y,-1),add(exp_ad(scale(X,-1),Y,N),scale(Y,-1)),N)
    C = {}
    for n in range(2,N+1):
        C[n] = scale(grade(F,n),Q(1,n))
        F = add(exp_ad(scale(C[n],-1),F,N),scale(C[n],-n))
    return C


def partitions(n: int, minimum: int = 2) -> Iterable[tuple[int,...]]:
    """Nondecreasing partitions with parts >= minimum."""
    if n == 0:
        yield ()
    for first in range(minimum,n+1):
        for tail in partitions(n-first,first):
            yield (first,)+tail


def zassenhaus_forward(H: Poly, N: int) -> dict[int,Poly]:
    C={}
    for n in range(2,N+1):
        lower={}
        for parts in partitions(n):
            if len(parts)<2:
                continue
            term=ONE.copy()
            denominator=1
            for j in set(parts):
                denominator*=factorial(parts.count(j))
            for j in parts:
                term=mul(term,C[j],n)
            lower=add(lower,scale(term,Q(1,denominator)))
        C[n]=add(grade(H,n),scale(lower,-1))
    return C


@lru_cache(None)
def weighted_trees(n: int) -> tuple:
    """Enumerate all weighted plane trees of the paper, including a root leaf."""
    result = [(n, ())]
    for parts in partitions(n):
        if len(parts) < 2:
            continue
        for children in product(*(weighted_trees(j) for j in parts)):
            result.append((n, children))
    return tuple(result)


def zassenhaus_tree_formula(H: Poly, N: int) -> dict[int, Poly]:
    """Evaluate the finite, nonrecursive tree sum, without substituting C_j."""
    hs = {n: grade(H,n) for n in range(2,N+1)}
    def flatten(tree):
        weight, children = tree
        if not children:
            return Q(1), (weight,)
        denominator = 1
        child_weights = [child[0] for child in children]
        for j in set(child_weights):
            denominator *= factorial(child_weights.count(j))
        coefficient, leaves = Q(-1,denominator), ()
        for child in children:
            c, l = flatten(child)
            coefficient *= c
            leaves += l
        return coefficient, leaves
    ans = {}
    for n in range(2,N+1):
        total = {}
        for tree in weighted_trees(n):
            coefficient, leaves = flatten(tree)
            term = ONE.copy()
            for j in leaves:
                term = mul(term,hs[j],n)
            total = add(total,scale(term,coefficient))
        ans[n] = total
    return ans


def coproduct_primitive(p: Poly) -> bool:
    out: dict[tuple[str,str],Q]={}
    for w,a in p.items():
        for mask in range(1<<len(w)):
            u=''.join(c for i,c in enumerate(w) if mask&(1<<i))
            v=''.join(c for i,c in enumerate(w) if not mask&(1<<i))
            if not u or not v:
                continue
            out[u,v]=out.get((u,v),Q(0))+a
    return not any(out.values())


def polynomial_json(p: Poly) -> dict[str,str]:
    return {w:str(p[w]) for w in sorted(p,key=lambda w:(len(w),w))}


def main() -> None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--degree',type=int,default=10)
    parser.add_argument('--output',type=Path,default=Path('data'))
    args=parser.parse_args()
    N=args.degree
    if not 6<=N<=12:
        parser.error('--degree must be between 6 and 12 (exponential-size calculation)')
    args.output.mkdir(parents=True,exist_ok=True)
    checks=[]
    def check(name: str, ok: bool):
        if not ok:
            raise AssertionError(name)
        checks.append({'test':name,'status':'PASS'})
        print('PASS:',name,flush=True)
    E=mul(exp(X,N),exp(Y,N),N)
    Z=log(E,N)
    check('exp(log(exp(X)exp(Y))) = exp(X)exp(Y), through degree '+str(N),exp(Z,N)==E)
    check('Independent Bernoulli differential recurrence, through degree '+str(N),bch_recurrence(N)==Z)
    check('Right Dynkin projection fixes every homogeneous BCH component, through degree '+str(N),dynkin_projection(Z)==Z)
    check('Every displayed Wikipedia BCH coefficient through degree six',page_polynomial()=={w:a for w,a in Z.items() if len(w)<=6})
    cut_N=min(N,8)
    check('Independent nonrecursive word-cut coefficients through degree '+str(cut_N),
          all(cut_coefficient(''.join(w))==Z.get(''.join(w),0)
              for n in range(1,cut_N+1) for w in product('XY',repeat=n)))
    swap=lambda w:w.translate(str.maketrans('XY','YX'))
    check('Swap parity identity, through degree '+str(N),
          all(Z.get(swap(w),0)==(-1)**(len(w)+1)*a for w,a in Z.items()))
    check('Word-reversal parity identity, through degree '+str(N),
          all(Z.get(w[::-1],0)==(-1)**(len(w)+1)*a for w,a in Z.items()))
    check('Primitive BCH coproduct (independent unshuffle), through degree '+str(cut_N),
          coproduct_primitive({w:a for w,a in Z.items() if len(w)<=cut_N}))
    C,H=zassenhaus_residual(N)
    check('Zassenhaus residual and adjoint-differential algorithms agree through degree '+str(N),C==zassenhaus_differential(N))
    check('Zassenhaus forward partition recurrence agrees through degree '+str(N),C==zassenhaus_forward(H,N))
    check('Explicit weighted-tree Zassenhaus sum agrees through degree '+str(N),C==zassenhaus_tree_formula(H,N))
    check('Zassenhaus right Dynkin projection, through degree '+str(N),all(dynkin_projection(c)==c for c in C.values()))
    factors=E
    for n in range(2,N+1):
        factors=mul(factors,exp(C[n],N),N)
    check('Complete Zassenhaus product identity, through degree '+str(N),factors==exp(add(X,Y),N))
    page_C={2:scale(right_bracket('XY'),-Q(1,2)),
            3:add(scale(right_bracket('YXY'),Q(1,3)),scale(right_bracket('XXY'),Q(1,6))),
            4:add(scale(right_bracket('XXXY'),-Q(1,24)),scale(right_bracket('YXXY'),-Q(1,8)),scale(right_bracket('YYXY'),-Q(1,8)))}
    check('Displayed Zassenhaus exponents C2, C3, C4',all(C[n]==v for n,v in page_C.items()))
    sym=log(mul(mul(exp(scale(X,Q(1,2)),N),exp(Y,N),N),exp(scale(X,Q(1,2)),N),N),N)
    check('Symmetric product has no even logarithmic terms',all(len(w)%2 for w in sym))
    cubic=add(scale(right_bracket('XXY'),-Q(1,24)),scale(right_bracket('YXY'),-Q(1,12)))
    check('Symmetric cubic logarithm',grade(sym,3)==cubic)
    check('Hadamard conjugation through degree '+str(N),
          mul(mul(exp(X,N),Y,N),exp(scale(X,-1),N),N)==exp_ad(X,Y,N))
    # Coordinate-free Maurer--Cartan power series coefficient identity.
    b=bernoulli_coefficients(N)
    check('Bernoulli inverse phi_- * f = 1 through degree '+str(N),
          all(sum((Q((-1)**j,factorial(j+1))*b[n-j] for j in range(n+1)),Q(0))==(1 if n==0 else 0) for n in range(N+1)))
    check('Invariant metric even-series coefficient identity through degree '+str(N),
          all(sum((Q((-1)**j,factorial(j+1)*factorial(n-j+1)) for j in range(n+1)),Q(0))==(Q(2,factorial(n+2)) if n%2==0 else 0) for n in range(N+1)))
    # A three-letter formal associativity check, deliberately independent of matrices.
    K=min(N,6)
    T={'T':Q(1)}
    BCH=lambda p,q:log(mul(exp(p,K),exp(q,K),K),K)
    check('Three-letter BCH associativity through degree '+str(K),BCH(BCH(X,Y),T)==BCH(X,BCH(Y,T)))
    (args.output/'bch_coefficients.json').write_text(json.dumps(polynomial_json(Z),indent=2)+'\n')
    (args.output/'zassenhaus_coefficients.json').write_text(json.dumps({str(n):polynomial_json(c) for n,c in C.items()},indent=2)+'\n')
    (args.output/'symmetric_bch_coefficients.json').write_text(json.dumps(polynomial_json(sym),indent=2)+'\n')
    with (args.output/'bch_words.tsv').open('w',newline='') as f:
        wr=csv.writer(f,delimiter='\t');wr.writerow(['degree','word','coefficient'])
        for w in sorted(Z,key=lambda w:(len(w),w)):
            wr.writerow([len(w),w,str(Z[w])])
    counts=[{'degree':n,'nonzero_BCH_words':len(grade(Z,n)),
             'nonzero_Zassenhaus_words':len(C.get(n,{})),
             'weighted_Zassenhaus_trees':len(weighted_trees(n)) if n>=2 else 0} for n in range(1,N+1)]
    results={'arithmetic':'exact fractions over the free associative algebra',
             'maximum_degree':N,'checks':checks,'counts':counts,
             'scope':'Finite checks support, but do not replace, the all-orders proofs in the paper.'}
    (args.output/'verification_results.json').write_text(json.dumps(results,indent=2)+'\n')
    # Human-readable table used by the LaTeX paper.
    with (args.output/'word_certificate.tex').open('w') as f:
        for n in (5,6):
            words=[''.join(w) for w in product('XY',repeat=n)]
            groups=[words[i:i+16] for i in range(0,len(words),16)]
            f.write('\\subsection*{Degree '+str(n)+' word coefficients}\n')
            f.write('\\begin{center}\\small\\begin{tabular}{'+('lr'*len(groups))+'}\\toprule\n')
            f.write(' & '.join(['Word & Coefficient']*len(groups))+'\\\\\\midrule\n')
            for row in range(16):
                cells=[]
                for group in groups:
                    w=group[row];a=Z.get(w,Q(0))
                    astr=str(a) if a.denominator==1 else ('-' if a<0 else '')+'\\tfrac{'+str(abs(a.numerator))+'}{'+str(a.denominator)+'}'
                    cells.extend(['\\texttt{'+w+'}','$'+astr+'$'])
                f.write(' & '.join(cells)+'\\\\\n')
            f.write('\\bottomrule\\end{tabular}\\end{center}\n')
    print(json.dumps(counts,indent=2))

if __name__=='__main__':
    main()
