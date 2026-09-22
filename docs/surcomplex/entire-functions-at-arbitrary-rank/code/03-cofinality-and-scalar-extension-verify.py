#!/usr/bin/env python3
"""Finite exact regression tests accompanying the cofinality article.

Uses only Python's standard library.  No numerical approximations or sampling
of the surreal field is performed.  These checks do not prove the transfinite
support lemmas, cofinality theorems, or infinite factorization theorem.
"""
from __future__ import annotations
from fractions import Fraction as Q
from itertools import combinations
from pathlib import Path
import json

CHECKS: list[str] = []

def check(condition: bool, description: str) -> None:
    if not condition:
        raise AssertionError(description)
    CHECKS.append(description)

# Exponents are finite vectors.  The highest indexed nonzero coordinate
# determines the sign: e_(j+1) dominates every integral multiple of e_j.
Exponent = tuple[Q, ...]
Hahn = dict[Exponent, Q]

def key(a: Exponent) -> tuple[Q, ...]:
    return tuple(reversed(a))

def add_exp(a: Exponent, b: Exponent) -> Exponent:
    if len(a) != len(b):
        raise ValueError("Exponents belong to different finite workspaces")
    return tuple(x+y for x,y in zip(a,b))

def scale_exp(a: Exponent, n: int | Q) -> Exponent:
    return tuple(Q(n)*x for x in a)

def unit(rank: int, j: int) -> Exponent:
    if not 0 <= j < rank:
        raise ValueError("Basis index out of range")
    return tuple(Q(int(k == j)) for k in range(rank))

def h_add(a: Hahn, b: Hahn) -> Hahn:
    out = dict(a)
    for e, c in b.items():
        out[e] = out.get(e, Q(0)) + c
        if not out[e]:
            del out[e]
    return out

def h_mul(a: Hahn, b: Hahn) -> Hahn:
    out: Hahn = {}
    for e,c in a.items():
        for f,d in b.items():
            g = add_exp(e,f)
            out[g] = out.get(g,Q(0)) + c*d
            if not out[g]:
                del out[g]
    return out

def h_val(a: Hahn) -> Exponent:
    if not a:
        raise ValueError("The zero series has valuation +infinity")
    return min(a, key=key)

def polynomial_product(n: int, rank: int) -> list[Hahn]:
    z = (Q(0),)*rank
    p: list[Hahn] = [{z: Q(1)}]
    for j in range(n):
        factor = {unit(rank,j): Q(-1)}
        out: list[Hahn] = [{} for _ in range(len(p)+1)]
        for k, a in enumerate(p):
            out[k] = h_add(out[k], a)
            out[k+1] = h_add(out[k+1], h_mul(a, factor))
        p = out
    return p

def evaluate_monomial(p: list[Hahn], exponent: Exponent) -> Hahn:
    ans: Hahn = {}
    for k, a in enumerate(p):
        shifted = {add_exp(e, scale_exp(exponent,k)): c for e,c in a.items()}
        ans = h_add(ans, shifted)
    return ans

def derivative(p: list[Hahn]) -> list[Hahn]:
    return [{e: k*c for e,c in p[k].items()} for k in range(1,len(p))]

# Exact polynomial arithmetic over Q for the preparation calculation.
Poly = list[Q]  # coefficient of X^j is at position j

def trim(p: Poly) -> Poly:
    while p and not p[-1]:
        p.pop()
    return p

def pa(a: Poly, b: Poly) -> Poly:
    out = [Q(0)] * max(len(a),len(b))
    for j,c in enumerate(a): out[j] += c
    for j,c in enumerate(b): out[j] += c
    return trim(out)

def ps(a: Poly, b: Poly) -> Poly:
    return pa(a,[-c for c in b])

def pm(a: Poly, b: Poly) -> Poly:
    if not a or not b: return []
    out = [Q(0)] * (len(a)+len(b)-1)
    for j,c in enumerate(a):
        for k,d in enumerate(b): out[j+k] += c*d
    return trim(out)

def pd(a: Poly, b: Poly) -> tuple[Poly, Poly]:
    if not b: raise ZeroDivisionError("Polynomial division by zero")
    r = list(a)
    q = [Q(0)] * max(0,len(a)-len(b)+1)
    while r and len(r) >= len(b):
        k = len(r)-len(b)
        c = r[-1]/b[-1]
        q[k] += c
        r = ps(r, [Q(0)]*k+[c*d for d in b])
    return trim(q),trim(r)

def main() -> dict:
    rank = 10
    zero = (Q(0),)*rank
    for n in range(1,9):
        p = polynomial_product(n,rank)
        for k in range(n+1):
            expect = tuple(Q(int(j < k)) for j in range(rank))
            check(h_val(p[k]) == expect, f"N={n}: coefficient {k} has predicted leading exponent")
            check(len(p[k]) == len(list(combinations(range(n),k))), f"N={n}: coefficient {k} subset count")
            check(all(c == (-1)**k for c in p[k].values()), f"N={n}: coefficient {k} signs")
        for j in range(n):
            root_exp = scale_exp(unit(rank,j),-1)
            check(not evaluate_monomial(p,root_exp),f"N={n}: root t^(-e_{j}) exact")
            check(bool(evaluate_monomial(derivative(p),root_exp)),f"N={n}: root {j} simple")
        samples = [zero]
        for j in range(n):
            s = scale_exp(unit(rank,j),-1)
            samples += [s,add_exp(s,scale_exp(unit(rank,0),Q(1,2))),
                        add_exp(s,scale_exp(unit(rank,0),Q(-1,2)))]
        for sample_index,s in enumerate(samples):
            weights = [add_exp(h_val(a),scale_exp(s,k)) for k,a in enumerate(p)]
            mu = min(weights,key=key)
            active = [k for k,w in enumerate(weights) if w == mu]
            expected_closed = sum(key(scale_exp(unit(rank,j),-1)) >= key(s) for j in range(n))
            expected_open = sum(key(scale_exp(unit(rank,j),-1)) > key(s) for j in range(n))
            check(max(active) == expected_closed,f"N={n}, radius {sample_index}: closed-ball Newton count")
            check(min(active) == expected_open,f"N={n}, radius {sample_index}: open-ball Newton count")
        outer = unit(rank,9)
        weights = [add_exp(h_val(p[k]),scale_exp(outer,-k)) for k in range(n+1)]
        check(all(key(weights[k+1]) < key(weights[k]) for k in range(n)),
              f"N={n}: descending valuations at a newly dominant scale")

    # Hidden-tail example in rank two: epsilon=e_0, eta=e_1.
    eps, eta = unit(2,0),unit(2,1)
    for n in range(1,101):
        first = scale_exp(eps,n*n)
        tail = add_exp(eta,scale_exp(eps,-n*n))
        check(key(first) < key(tail), f"hidden tail n={n}: same leading valuation")
    for lam in [Q(-7),Q(-1,2),Q(0),Q(3,2),Q(10)]:
        n0 = max(1,int(abs(lam))+1)
        for n in range(n0,n0+20):
            u = add_exp(eta,scale_exp(eps,n*lam-n*n))
            w = add_exp(eta,scale_exp(eps,(n+1)*lam-(n+1)**2))
            check(key(w) < key(u),f"hidden tail lambda={lam}, n={n}: descending subsequence")

    # Preparation: F=X^2-X+t(X^3+1), computed through t^8.
    order = 8
    p0 = [Q(0),Q(-1),Q(1)]
    E = [Q(1),Q(0),Q(0),Q(1)]
    R: list[Poly] = [[] for _ in range(order+1)]
    V: list[Poly] = [[] for _ in range(order+1)]
    for m in range(1,order+1):
        h = list(E) if m == 1 else []
        for a in range(1,m): h = ps(h,pm(R[a],V[m-a]))
        V[m],R[m] = pd(h,p0)
        check(len(R[m]) <= 2, f"preparation order {m}: remainder degree <2")
    P = [p0]+R[1:]
    U = [[Q(1)]]+V[1:]
    for m in range(order+1):
        actual: Poly = []
        for a in range(m+1): actual=pa(actual,pm(P[a],U[m-a]))
        target = p0 if m == 0 else E if m == 1 else []
        check(actual == target,f"preparation order {m}: coefficient identity")
    check(R[1] == [Q(1),Q(1)],"preparation first remainder X+1")
    check(R[2] == [Q(-1),Q(-3)],"preparation second remainder -3X-1")
    check(R[3] == [Q(2),Q(8)],"preparation third remainder 8X+2")

    output = {
        "status":"PASS",
        "checks_passed":len(CHECKS),
        "arithmetic":"exact integers and fractions; no floating point",
        "scope":"finite regression checks only; not a proof of infinite or cofinal statements",
        "preparation_remainders": [[str(c) for c in p] for p in R[1:]],
        "preparation_quotients": [[str(c) for c in p] for p in V[1:]],
        "checks":CHECKS,
    }
    output_dir = Path(__file__).resolve().parents[1] / "data"
    output_dir.mkdir(exist_ok=True)
    (output_dir/"verification.json").write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8")
    summary = f"PASS: {len(CHECKS)} exact finite checks.\n"+output["scope"]+"\n"
    (output_dir/"verification.txt").write_text(summary,encoding="utf-8")
    print(summary,end="")
    return output

if __name__ == "__main__":
    main()
