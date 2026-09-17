#!/usr/bin/env python3
"""Exact BCH and Zassenhaus calculations in Q< X,Y >.

Only the Python standard library is required (Python 3.9+).
A polynomial is a sparse dictionary {word: Fraction}; the empty word is 1.
All operations are truncated by total word length. No floating-point arithmetic
is used in the algebraic verification. Run --help for options.
"""
from __future__ import annotations
import argparse
import csv
import json
from fractions import Fraction as Q
from functools import lru_cache
from itertools import product
from math import comb, factorial
from pathlib import Path
from time import perf_counter
from typing import Dict, List, Tuple

Poly = Dict[str, Q]
ONE: Poly = {"": Q(1)}
X: Poly = {"X": Q(1)}
Y: Poly = {"Y": Q(1)}


def clean(p: Poly) -> Poly:
    return {w: c for w, c in p.items() if c}


def add(*ps: Poly) -> Poly:
    out: Poly = {}
    for p in ps:
        for w, c in p.items():
            out[w] = out.get(w, Q(0)) + c
    return clean(out)


def scale(p: Poly, c: Q) -> Poly:
    return clean({w: a * c for w, a in p.items()})


def mul(p: Poly, q: Poly, degree: int) -> Poly:
    # Degree buckets avoid traversing pairs which truncation would discard.
    left: Dict[int, List[Tuple[str,Q]]] = {}
    right: Dict[int, List[Tuple[str,Q]]] = {}
    for u,a in p.items():
        left.setdefault(len(u),[]).append((u,a))
    for v,b in q.items():
        right.setdefault(len(v),[]).append((v,b))
    out: Poly = {}
    for i,us in left.items():
        for j,vs in right.items():
            if i+j>degree:
                continue
            for u,a in us:
                for v,b in vs:
                    w=u+v
                    out[w]=out.get(w,Q(0))+a*b
    return clean(out)


def bracket(p: Poly, q: Poly, degree: int) -> Poly:
    return add(mul(p, q, degree), scale(mul(q, p, degree), Q(-1)))


def homogeneous(p: Poly, n: int) -> Poly:
    return {w: c for w, c in p.items() if len(w) == n}


def truncate(p: Poly, n: int) -> Poly:
    return {w: c for w, c in p.items() if len(w) <= n}


def exp_series(p: Poly, degree: int) -> Poly:
    if p.get("", 0):
        raise ValueError("exp_series requires zero constant term")
    out, term = dict(ONE), dict(ONE)
    for k in range(1, degree + 1):
        term = scale(mul(term, p, degree), Q(1, k))
        if not term:
            break
        out = add(out, term)
    return out


def log_series(p: Poly, degree: int) -> Poly:
    if p.get("", 0) != 1:
        raise ValueError("log_series requires constant term 1")
    q = add(p, scale(ONE, Q(-1)))
    out, term = {}, dict(ONE)
    for k in range(1, degree + 1):
        term = mul(term, q, degree)
        if not term:
            break
        out = add(out, scale(term, Q((-1) ** (k - 1), k)))
    return out


def exp_ad(a: Poly, p: Poly, degree: int) -> Poly:
    out, term = dict(p), dict(p)
    for k in range(1, degree + 1):
        term = scale(bracket(a, term, degree), Q(1, k))
        if not term:
            break
        out = add(out, term)
    return out


@lru_cache(maxsize=None)
def right_word(w: str) -> Poly:
    if not w:
        return {}
    if len(w) == 1:
        return {w: Q(1)}
    return bracket({w[0]: Q(1)}, right_word(w[1:]), len(w))


def right_projection(p: Poly) -> Poly:
    out: Poly = {}
    for w, c in p.items():
        if w:
            out = add(out, scale(right_word(w), c / len(w)))
    return out


def bernoulli_plus_coefficients(n: int) -> List[Q]:
    """b_k = B_k^+/k!, so b_1=+1/2."""
    b = [Q(1)]
    for k in range(1, n + 1):
        b.append(-sum((b[j] * Q((-1) ** (k-j), factorial(k-j+1))
                       for j in range(k)), Q(0)))
    return b


def block_weight(w: str) -> Q:
    """Coefficient of w in exp(X)exp(Y)-1 for a nonempty word."""
    if not w or "YX" in w:
        return Q(0)
    return Q(1, factorial(w.count("X")) * factorial(w.count("Y")))


def cut_coefficient(w: str) -> Q:
    """Independent finite cut formula for one associative BCH coefficient."""
    n = len(w)
    dp: List[List[Q]] = [[Q(0) for _ in range(n+1)] for _ in range(n+1)]
    dp[0][0] = Q(1)
    for end in range(1, n+1):
        for start in range(end):
            a = block_weight(w[start:end])
            if a:
                for k in range(1, end+1):
                    dp[end][k] += dp[start][k-1] * a
    return sum((Q((-1)**(k-1), k)*dp[n][k] for k in range(1, n+1)), Q(0))


def integral_bch(degree: int) -> Poly:
    """Poincare integral, evaluated by powers of exp(adX)exp(t adY)-I.

    Starting from Y, a monomial with q Ys has t-degree q-1; integration
    therefore divides its coefficient by q. This tracks t without a second
    polynomial type and is independent of the associative log calculation.
    """
    out, term = add(X, Y), dict(Y)
    for k in range(1, degree):
        term = add(exp_ad(X, exp_ad(Y, term, degree), degree), scale(term, Q(-1)))
        if not term:
            break
        integrated = {w: c / w.count("Y") for w, c in term.items()}
        out = add(out, scale(integrated, Q((-1)**(k+1), k*(k+1))))
    return out


def quadratic_y_formula(degree: int) -> Poly:
    """All-X, exactly-two-Y formula using the bivariate kernel K(u,v)."""
    b = bernoulli_plus_coefficients(degree+1)
    iterates = [dict(Y)]
    for _ in range(degree):
        iterates.append(bracket(X, iterates[-1], degree))
    out: Poly = {}
    # K(u,v)=h(u)/(2u)*(h(u+v)-h(v)).
    for p in range(degree-1):
        for q in range(degree-1-p):
            if p+q+2 > degree:
                continue
            coefficient = sum((b[a]*b[p+q+1-a]*comb(p+q+1-a, p+1-a)/2
                               for a in range(p+1)), Q(0))
            if coefficient:
                out = add(out, scale(bracket(iterates[p], iterates[q], degree), coefficient))
    return out


def zassenhaus_residual(degree: int) -> Dict[int, Poly]:
    r = mul(mul(exp_series(scale(Y,Q(-1)),degree),
                exp_series(scale(X,Q(-1)),degree),degree),
            exp_series(add(X,Y),degree),degree)
    cs: Dict[int, Poly] = {}
    for n in range(2, degree+1):
        cs[n] = homogeneous(r,n)
        r = mul(exp_series(scale(cs[n],Q(-1)),degree),r,degree)
        if any(0<len(w)<=n for w in r):
            raise AssertionError(f"Zassenhaus residual not removed at degree {n}")
    if r != ONE:
        raise AssertionError("Zassenhaus residual did not reduce to 1")
    return cs


def zassenhaus_lie(degree: int) -> Dict[int, Poly]:
    # F1=exp(-adY)(exp(-adX)-I)Y. A word of length k+1 is
    # the coefficient of t^k in F1.
    f = exp_ad(scale(Y,Q(-1)),
               add(exp_ad(scale(X,Q(-1)),Y,degree),scale(Y,Q(-1))),degree)
    cs: Dict[int, Poly] = {}
    for n in range(2,degree+1):
        cs[n] = scale(homogeneous(f,n),Q(1,n))
        f = exp_ad(scale(cs[n],Q(-1)),
                   add(f,scale(cs[n],Q(-n))),degree)
    return cs


def is_lyndon(w: str) -> bool:
    return bool(w) and all(w < w[i:] for i in range(1,len(w)))


@lru_cache(maxsize=None)
def lyndon_bracket(w: str) -> Poly:
    if len(w)==1:
        return {w:Q(1)}
    if not is_lyndon(w):
        raise ValueError(f"Not a Lyndon word: {w}")
    # Earliest split = longest proper Lyndon suffix.
    i=next(i for i in range(1,len(w)) if is_lyndon(w[i:]))
    return bracket(lyndon_bracket(w[:i]),lyndon_bracket(w[i:]),len(w))


def lyndon_coordinates(p: Poly, n: int) -> Dict[str,Q]:
    r=homogeneous(p,n)
    coeffs: Dict[str,Q]={}
    for chars in product("XY",repeat=n):
        w="".join(chars)
        if is_lyndon(w):
            c=r.get(w,Q(0))
            if c:
                coeffs[w]=c
                r=add(r,scale(lyndon_bracket(w),-c))
    if r:
        raise AssertionError(f"Nonzero Lyndon reconstruction residual at degree {n}: {r}")
    rebuilt: Poly = {}
    for w, c in coeffs.items():
        rebuilt = add(rebuilt, scale(lyndon_bracket(w), c))
    if rebuilt != homogeneous(p, n):
        raise AssertionError(f"Lyndon table reconstruction failed at degree {n}")
    return coeffs


def primitive_remainder(p: Poly) -> Dict[Tuple[str,str],Q]:
    """Reduced coproduct, with both tensor factors nonempty."""
    out: Dict[Tuple[str,str],Q]={}
    for w,c in p.items():
        n=len(w)
        for mask in range(1,(1<<n)-1):
            a="".join(w[i] for i in range(n) if mask&(1<<i))
            b="".join(w[i] for i in range(n) if not mask&(1<<i))
            key=(a,b)
            out[key]=out.get(key,Q(0))+c
    return {k:v for k,v in out.items() if v}


def page_terms() -> Dict[int,Poly]:
    def R(w:str,c:Q=Q(1))->Poly:
        return scale(right_word(w),c)
    return {
        1:add(X,Y),
        2:R("XY",Q(1,2)),
        3:add(R("XXY",Q(1,12)),R("YYX",Q(1,12))),
        4:R("YXXY",Q(-1,24)),
        5:add(R("YYYYX",Q(-1,720)),R("XXXXY",Q(-1,720)),
              R("XYYYX",Q(1,360)),R("YXXXY",Q(1,360)),
              R("YXYXY",Q(1,120)),R("XYXYX",Q(1,120))),
        6:add(R("XYXYXY",Q(1,240)),R("XYXXXY",Q(1,720)),
              R("XXYYXY",Q(-1,720)),R("XYYYXY",Q(1,1440)),
              R("XXYXXY",Q(-1,1440)))
    }


def compare(label:str,a:Poly,b:Poly,results:list,degree:int)->None:
    diff=add(a,scale(b,Q(-1)))
    if diff:
        first=sorted(diff,key=lambda w:(len(w),w))[0]
        raise AssertionError(f"{label}: coefficient of {first} differs by {diff[first]}")
    results.append({"test":label,"through_degree":degree,"status":"PASS"})


def run(degree:int, check_degree:int, outdir:Path)->dict:
    start=perf_counter()
    outdir.mkdir(parents=True,exist_ok=True)
    p=mul(exp_series(X,degree),exp_series(Y,degree),degree)
    z=log_series(p,degree)
    cs=zassenhaus_residual(degree)
    results=[]
    compare("exp(log(exp(X)exp(Y)))",exp_series(z,degree),p,results,degree)
    for n,known in page_terms().items():
        if n<=degree:
            compare(f"page BCH homogeneous degree {n}",homogeneous(z,n),known,results,n)
    small=truncate(z,check_degree)
    compare("Poincare integral versus associative logarithm",integral_bch(check_degree),small,results,check_degree)
    compare("Dynkin-Specht-Wever projection",right_projection(small),small,results,check_degree)
    compare("quadratic-in-Y generating kernel",quadratic_y_formula(check_degree),
            {w:c for w,c in small.items() if w.count("Y")==2},results,check_degree)
    b=bernoulli_plus_coefficients(degree)
    one_y={}
    for k in range(degree):
        one_y=add(one_y,scale(right_word("X"*k+"Y"),b[k]))
    compare("all-X linear-in-Y Bernoulli series",one_y,
            {w:c for w,c in z.items() if w.count("Y")==1},results,degree)
    swap={w.translate(str.maketrans("XY","YX")):c for w,c in z.items()}
    parity={w:((-1)**(len(w)+1))*c for w,c in z.items()}
    compare("exchange parity",swap,parity,results,degree)
    for n in range(1,check_degree+1):
        if primitive_remainder(homogeneous(z,n)):
            raise AssertionError(f"Nonzero reduced coproduct in degree {n}")
    results.append({"test":"primitive coproduct","through_degree":check_degree,"status":"PASS"})
    # Independent scalar word-cut evaluation, including zero coefficients.
    words_checked=0
    for n in range(1,check_degree+1):
        for chars in product("XY",repeat=n):
            w="".join(chars)
            if cut_coefficient(w)!=z.get(w,Q(0)):
                raise AssertionError(f"Cut formula failed for {w}")
            words_checked+=1
    results.append({"test":"finite word-cut formula (including zeros)",
                    "through_degree":check_degree,"words_checked":words_checked,"status":"PASS"})
    cs_lie=zassenhaus_lie(check_degree)
    for n in range(2,check_degree+1):
        compare(f"Zassenhaus residual versus Lie recurrence C{n}",
                cs[n],cs_lie[n],results,n)
    prod=mul(exp_series(X,degree),exp_series(Y,degree),degree)
    for n in range(2,degree+1):
        prod=mul(prod,exp_series(cs[n],degree),degree)
    compare("ordered Zassenhaus product",prod,exp_series(add(X,Y),degree),results,degree)
    if degree>=4:
        c2=scale(right_word("XY"),Q(-1,2))
        c3=add(scale(right_word("XXY"),Q(1,6)),scale(right_word("YXY"),Q(1,3)))
        c4=add(scale(right_word("XXXY"),Q(-1,24)),scale(right_word("YXXY"),Q(-1,8)),
               scale(right_word("YYXY"),Q(-1,8)))
        for n,c in [(2,c2),(3,c3),(4,c4)]:
            compare(f"page Zassenhaus C{n}",cs[n],c,results,n)
    strang=log_series(mul(mul(exp_series(scale(X,Q(1,2)),degree),exp_series(Y,degree),degree),
                         exp_series(scale(X,Q(1,2)),degree),degree),degree)
    if any(len(w)%2==0 for w in strang):
        raise AssertionError("Strang logarithm contains an even degree")
    results.append({"test":"Strang logarithm oddness","through_degree":degree,"status":"PASS"})
    if degree>=3:
        e3=add(scale(right_word("XXY"),Q(-1,24)),scale(right_word("YXY"),Q(-1,12)))
        compare("Strang cubic defect",homogeneous(strang,3),e3,results,3)
    # Reconstruct all exported Lyndon expansions exactly; their use does not
    # rely on floating point or on a precomputed coefficient table.
    lyndon={n:lyndon_coordinates(z,n) for n in range(1,degree+1)}
    zlyndon={n:lyndon_coordinates(cs[n],n) for n in range(2,degree+1)}
    slyndon={n:lyndon_coordinates(strang,n) for n in range(1,degree+1)}
    results.append({"test":"all exported Lyndon reconstructions (BCH, Zassenhaus, Strang)",
                    "through_degree":degree,"status":"PASS"})
    def export_words(name:str,polys:Dict[int,Poly],right:bool=False)->None:
        with (outdir/name).open("w",newline="",encoding="utf-8") as f:
            writer=csv.writer(f)
            writer.writerow(["degree","word","numerator","denominator"])
            for n,pn in sorted(polys.items()):
                for w,c in sorted(pn.items()):
                    if right:
                        if len(w)>1 and w[-1]==w[-2]:
                            continue
                        c/=n
                    writer.writerow([n,w,c.numerator,c.denominator])
    homogeneous_z={n:homogeneous(z,n) for n in range(1,degree+1)}
    export_words("bch_associative.csv",homogeneous_z)
    export_words("bch_right_commutators.csv",homogeneous_z,True)
    export_words("bch_lyndon.csv",lyndon)
    export_words("zassenhaus_associative.csv",cs)
    export_words("zassenhaus_lyndon.csv",zlyndon)
    export_words("strang_lyndon.csv",slyndon)
    with (outdir/"bernoulli_plus.csv").open("w",newline="",encoding="utf-8") as f:
        wr=csv.writer(f);wr.writerow(["n","numerator_Bn_over_nfactorial","denominator_Bn_over_nfactorial"])
        for n,c in enumerate(b):wr.writerow([n,c.numerator,c.denominator])
    report={"arithmetic":"exact fractions.Fraction over Q", "table_degree":degree,
            "independent_cross_check_degree":check_degree,
            "tests":results,
            "counts":[{"degree":n,"bch_nonzero_words":len(homogeneous_z[n]),
                       "bch_nonzero_lyndon":len(lyndon[n]),
                       "zassenhaus_nonzero_lyndon":len(zlyndon.get(n,{}))}
                      for n in range(1,degree+1)],
            "elapsed_seconds":round(perf_counter()-start,3)}
    (outdir/"verification_report.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
    return report


def main()->None:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--degree",type=int,default=12,help="table and reconstruction degree (default 12)")
    parser.add_argument("--check-degree",type=int,default=10,help="independent cross-check degree (default 10)")
    parser.add_argument("--out",type=Path,default=Path(__file__).resolve().parent.parent/"data")
    args=parser.parse_args()
    if not 1<=args.check_degree<=args.degree<=16:
        parser.error("require 1 <= check-degree <= degree <= 16; costs grow exponentially")
    report=run(args.degree,args.check_degree,args.out)
    print(json.dumps(report,indent=2))

if __name__=="__main__":
    main()
