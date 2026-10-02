#!/usr/bin/env python3
from itertools import combinations, permutations
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
import hashlib, json

R = [{2,3,4},{0,1,4},{1,3},{4}]
ZERO = (0,0,0,0,0)

def add(*terms):
    result = defaultdict(Fraction)
    for sign, p in terms:
        for e, c in p.items(): result[e] += sign*c
    return {e:c for e,c in result.items() if c}

def mul(p, q):
    out = defaultdict(Fraction)
    for e,c in p.items():
        for f,d in q.items():
            out[tuple(a+b for a,b in zip(e,f))] += c*d
    return {e:c for e,c in out.items() if c}

def basis(tails):
    out = {}
    for hs in combinations(range(5),len(tails)):
        if any(all(h in R[t] for t,h in zip(tails,p)) for p in permutations(hs)):
            out[tuple(int(i in hs) for i in range(5))] = Fraction(1)
    return out

def variable(i):
    return {tuple(int(j==i) for j in range(5)):Fraction(1)}

def main():
    p,q,r,s = [basis(t) for t in [(0,1,2),(0,1,3),(0,1),(0,1,2,3)]]
    gap = add((1,mul(p,q)),(-1,mul(r,s)))
    assert gap[(1,1,1,1,2)] == -1
    a,b,c,d,e = [variable(i) for i in range(5)]
    first = add((1,mul(a,d)),(Fraction(1,2),mul(b,d)),(-Fraction(1,2),mul(b,c)))
    second = add((1,mul(b,c)),(1,mul(b,d)))
    sos = mul(mul(e,e),add((1,mul(first,first)),(Fraction(3,4),mul(second,second))))
    assert gap == sos
    result = {
        'verdict':'PASS',
        'tail_neighborhoods':[[chr(97+j) for j in sorted(row)] for row in R],
        'role_cover':{'tails':[0,1],'heads':['b','d','e']},
        'basis_counts':[len(p),len(q),len(r),len(s)],
        'negative_coefficient':{'head_exponents':[1,1,1,1,2],'coefficient':-1},
        'exact_rational_SOS_verified':True,
        'gap_terms':[{'exponents':list(k),'coefficient':str(v)} for k,v in sorted(gap.items())],
        'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    }
    Path(__file__).with_name('four_core_obstruction_receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
