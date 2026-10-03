#!/usr/bin/env python3
"""Deterministic exact-arithmetic checks; run from any working directory.

Writes verification.json and complete worked examples. These checks support
but do not replace the unbounded proofs in article.tex.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import product
from math import gcd
from pathlib import Path
import json
import random
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "src"))
from substrate import *

COUNTS: Counter[str] = Counter()


def check(group: str, condition: bool, details: object = None) -> None:
    if not condition:
        raise AssertionError((group, details))
    COUNTS[group] += 1


def rejects(fn, *args) -> bool:
    try:
        fn(*args)
    except (ValueError, TypeError):
        return True
    return False


def determinant(a: list[list[int]]) -> Fraction:
    a = [[Fraction(x) for x in row] for row in a]
    n = len(a)
    ans = Fraction(1)
    for j in range(n):
        pivot = next((k for k in range(j, n) if a[k][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            ans = -ans
        d = a[j][j]
        ans *= d
        for k in range(j + 1, n):
            ratio = a[k][j] / d
            for l in range(j + 1, n):
                a[k][l] -= ratio * a[j][l]
    return ans


def run() -> dict:
    rng = random.Random(20261002)
    programs = [countdown(), divergent(), transfer(), Program(1, (Instruction("HALT"),)),
                Program(1, (Instruction("TEST", 0, 2, 1), Instruction("INC", 0, 1), Instruction("HALT")))]
    for p in programs:
        for n in range(240):
            v = decode_node(p, n)
            check("node_coding", encode_node(p, v) == n)
            w = p.successor(v)
            if w is not None:
                check("reversible_history", p.predecessor(w) == v and w.history > v.history)
            pred = p.predecessor(v)
            if pred is not None:
                check("reversible_history", p.successor(pred) == v and pred.history < v.history)
        for n in range(500):
            nb = connected_neighbors(p, n)
            check("connected_graph", 1 <= len(nb) <= 3 and len(nb) == len(set(nb)) and n not in nb)
            check("connected_graph", all(n in connected_neighbors(p, w) for w in nb))
            check("connected_graph", set(map(swap, nb)) == set(connected_neighbors(p, swap(n))))
        for n in range(50):
            # Every rail/coupling node reaches the backbone in <= 2 edges.
            check("backbone_attachment", 4*n+2 in connected_neighbors(p, 4*n) and 4*n+3 in connected_neighbors(p, 4*n+2))
            check("backbone_attachment", 4*(n+1)+3 in connected_neighbors(p, 4*n+3))
    for p in programs:
        for c in product(range(4), repeat=p.dimension):
            check("input_roots", p.predecessor(p.root(c)) is None)
    for m in [3, 5, 7, 9, 11]:
        for L in range(1, 31):
            D = continuant(m, L)
            z = [continuant(m, L-i-1) for i in range(L)]
            check("continuants", z[-1] == 1 and gcd(D, z[0]) == 1)
            for i in range(L):
                check("continuants", m*z[i] - (z[i-1] if i else 0) - (z[i+1] if i+1<L else 0) == (D if i == 0 else 0))
            if L <= 10:
                matrix = [[m if i == j else -1 if abs(i-j) == 1 else 0 for j in range(L)] for i in range(L)]
                check("determinants", determinant(matrix) == D)
            if L > 1:
                check("root_monotonicity", Fraction(z[0], D) > Fraction(continuant(m,L-2), continuant(m,L-1)))
            check("lucas_growth", lucas_u(m, L+1) >= (m-1)**L)
    # Fibonacci specialization.
    fib = [0, 1]
    for _ in range(85): fib.append(fib[-1] + fib[-2])
    for L in range(40):
        check("fibonacci_specialization", continuant(3, L) == fib[2*L+2])
    for p in programs:
        for c in product(range(4), repeat=p.dimension):
            tr = p.trace(c, 15)
            if tr[-1].state != p.halt:
                continue
            T = len(tr)-1
            for m in [5, 7]:
                charge, z = canonical_network_certificate(p, c, T, m)
                root = 4*encode_node(p, p.root(c))
                check("complete_network_equations", apply_operator(p, z, m) == {root: charge, root+1: -charge})
                check("complete_network_equations", len(z) == 2*(T+1) and gcd(charge, *z.values()) == 1)
                for scale in [2, 3, 7]:
                    check("scaled_network_equations", apply_operator(p, {v: scale*a for v,a in z.items()}, m) == {root: scale*charge, root+1: -scale*charge})
                cert = compile_certificate(p, T, m)
                assignment = canonical_assignment(p, c, T, m)
                R = len(p.branches); Z = sum(i.op == "TEST" for i in p.instructions); d=p.dimension
                check("compiler_ledgers", len(cert.variables) == (d+3)*(T+1)+1+T*((d+1)*R+Z))
                check("compiler_ledgers", len(cert.rows) == d+5+T*(5+2*d+2*Z))
                check("compiler_ledgers", len(cert.cross_terms) == d*R*(R-1)*T)
                check("canonical_quadratic_zeros", cert.energy(assignment) == 0)
                check("canonical_quadratic_zeros", set(assignment) == set(cert.variables+cert.parameters))
                poly = cert.expanded()
                check("quadratic_degree", max(map(len,poly)) <= 2)
                for name in cert.variables + cert.parameters:
                    for delta in [-1, 1]:
                        if assignment[name]+delta < 0: continue
                        mutated = dict(assignment); mutated[name] += delta
                        check("single_coordinate_mutations", cert.energy(mutated) > 0, (name, delta))
                for _ in range(12):
                    random_values = {x:rng.randrange(-4,7) for x in cert.variables + cert.parameters}
                    expanded = sum(coef * (random_values[mon[0]] if len(mon)>0 else 1) * (random_values[mon[1]] if len(mon)>1 else 1) for mon,coef in poly.items())
                    check("expanded_polynomial_identities", cert.energy(random_values,natural=False) == expanded)
    # Truncation is not certification: the NEXT row detects leakage.
    p = divergent()
    for L in range(1, 20):
        tr = p.trace((0,), L)
        z={}
        for i, v in enumerate(tr[:L]):
            k=4*encode_node(p,v); z[k]=continuant(5,L-i-1); z[k+1]=-z[k]
        root=4*encode_node(p,tr[0]); nxt=4*encode_node(p,tr[L])
        check("exterior_leakage_counterexamples", apply_operator(p,z) == {root:continuant(5,L),root+1:-continuant(5,L),nxt:-1,nxt+1:1})
    # Exhaustive small natural routing gate tests, including cancellation traps.
    for R in [1,2,3]:
        for bs in product(range(3), repeat=R):
            for aa in product(range(3), repeat=R):
                E=(sum(bs)-1)**2 + sum(bs[s]*aa[r] for r in range(R) for s in range(R) if r!=s)
                expected=sum(bs)==1 and all(a==0 or bs[r]==1 for r,a in enumerate(aa))
                check("routing_gate_exhaustion", (E == 0)==expected)
    ps=[p for p in range(2,100) if is_prime(p)]
    for m in [3,5,7,9,11]:
        for p in ps:
            z=rank_of_apparition(m,p); vz=valuation(lucas_u(m,z),p)
            check("rank_bounds", 1 <= z <= p*p-1)
            for n in range(1,121):
                un=lucas_u(m,n)
                check("rank_divisibility", (un%p==0) == (n%z==0))
                if n%z==0:
                    check("valuation_lifting", valuation(un,p) == vz+valuation(n//z,p))
    localization_examples=[]
    for m in [3,5,7,9,11]:
        for S in [(),(2,),(3,),(2,3),(2,3,5),(2,3,5,7,11)]:
            info=localization_bound(m,S); B=info["first_excluded_length"]
            allowed=[]
            for L in range(1,max(100,B+10)):
                if smooth(continuant(m,L),S):
                    check("finite_prime_bounds", L < B,(m,S,L,B))
                    allowed.append(L)
                check("localization_majorant", all(valuation(lucas_u(m,L+1),p) <= r['c']+valuation(L+1,p) for p,r in zip(S, info['ranks'])))
            info["smooth_lengths_checked"] = allowed
            localization_examples.append(info)
    for p in programs:
        for c in product(range(3),repeat=p.dimension):
            for S in [(),(2,3),(2,3,5,7,11),(5,19,29)]:
                result=localized_membership(p,c,S,5)
                tr=p.trace(c,30)
                expected=tr[-1].state==p.halt and smooth(continuant(5,len(tr)),S)
                check("localization_decision_examples", result==expected)
    for bad in [-1, True, 1.0, "1"]:
        check("invalid_inputs", rejects(nat,bad))
        check("invalid_inputs", rejects(compile_certificate,countdown(),bad))
    for bad in [0,1,2,4,True,5.0]:
        check("invalid_inputs", rejects(lucas_u,bad,4))
    check("invalid_inputs",rejects(localization_bound,5,[4]))
    check("invalid_inputs",rejects(canonical_assignment,countdown(),(2,),4))
    check("invalid_inputs",rejects(canonical_assignment,divergent(),(0,),5))
    check("invalid_inputs",rejects(Program,1,(Instruction("HALT"),Instruction("HALT"))))
    example_p=countdown(); cert=compile_certificate(example_p,3)
    assignment=canonical_assignment(example_p,(2,),3)
    charge, network=canonical_network_certificate(example_p,(2,),3)
    (ROOT/'examples').mkdir(exist_ok=True)
    (ROOT/'examples'/'countdown_T3_polynomial.json').write_text(json.dumps(cert.export(),indent=2)+'\n')
    (ROOT/'examples'/'countdown_T3_witness.json').write_text(json.dumps({'assignment':assignment,'charge':charge,'network_values':network,'energy':cert.energy(assignment)},indent=2)+'\n')
    (ROOT/'examples'/'localization_bounds.json').write_text(json.dumps(localization_examples,indent=2)+'\n')
    report={'status':'passed','seed':20261002,'checks':dict(sorted(COUNTS.items())),'total_checks':sum(COUNTS.values()),
            'worked_example':{'T':3,'input':2,'m':5,'variables':len(cert.variables),'linear_residuals':len(cert.rows),'cross_terms':len(cert.cross_terms),'expanded_monomials':len(cert.expanded()),'degree':2,'charge':charge},
            'limits':'Finite checks only; no Lean verification, no exhaustive universality test, no numerical universal-machine table supplied.'}
    (ROOT/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    return report


if __name__ == '__main__':
    print(json.dumps(run(),indent=2))
