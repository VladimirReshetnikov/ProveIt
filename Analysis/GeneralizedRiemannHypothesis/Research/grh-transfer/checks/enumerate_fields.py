"""Enumerate finite Dirichlet character groups of total zero weight below 2.

Usage: python enumerate_fields.py quadratic.json nonreal.json > abelian_fields.json
Both inputs comprise records with character, q, B_lower and B_upper. The first
additionally gives B1_lower,B1_upper. Endpoints can be fractions or decimals.
The group keys are rational local angles as described in the report.
"""
from collections import Counter
from fractions import Fraction
from functools import cache
from math import lcm, prod, isqrt
import json
import sys

ONE = ()

def canonical(triples):
    key = tuple(sorted((int(p), Fraction(int(n),int(d)) % 1) for p,n,d in triples))
    if len(dict(key)) != len(key):
        raise ValueError("Repeated local coordinate")
    return tuple((p,z) for p,z in key if z)

@cache
def add(a,b):
    coords = dict(a)
    for p,z in b:
        coords[p] = (coords.get(p,0)+z) % 1
    return tuple(sorted((p,z) for p,z in coords.items() if z))

def encode(key):
    return [[p,z.numerator,z.denominator] for p,z in key]

def order(a):
    return lcm(*(z.denominator for _,z in a))

def generated(H,a):
    """Union H, H+a, H+2a,... until the next translate is again H."""
    G = set(H)
    v = a
    while v not in H:
        G.update(add(u,v) for u in H)
        v = add(v,a)
    return frozenset(G)

def invariant_factors(group):
    """Recover elementary divisors from cardinalities of p^k-torsion."""
    n = len(group)
    orders = [order(a) for a in group]
    factors = []
    for p in range(2,n+1):
        if n % p or any(p % j == 0 for j in range(2,isqrt(p)+1)):
            continue
        # p^k kills precisely those elements whose order divides p^k.
        k, old, counts = 1, 1, []
        while n % k == 0:
            k *= p
            count = sum(k % o == 0 for o in orders)
            delta = 0
            while count//old > p**delta:
                delta += 1
            counts.append(delta)
            old = count
            if not delta:
                break
        exps = []
        for i in range(1,len(counts)):
            exps.extend([p**i]*(counts[i-1]-counts[i]))
        factors.append(sorted(exps))
    size = max((len(f) for f in factors),default=0)
    inv = [1]*size
    for fs in factors:
        for i, x in enumerate(reversed(fs),start=1):
            inv[-i] *= x
    assert prod(inv) == len(group)
    return inv

def main():
    with open(sys.argv[1]) as h:
        quad = json.load(h)
    with open(sys.argv[2]) as h:
        comp = json.load(h)
    if isinstance(comp,dict):
        comp = comp['characters']
    data = {ONE:{"q":1,"character":[],"B_lower":quad["B1_lower"],"B_upper":quad["B1_upper"]}}
    for row in quad['characters']+comp:
        key = canonical(row['character'])
        if key in data or not key:
            raise ValueError(f"Duplicate or trivial input character: {row}")
        data[key] = row
    inputs = frozenset(data)
    by_size = lambda a:(int(data[a]["q"]),order(a),a)
    ranking = sorted(inputs-{ONE},key=by_size)
    for a in inputs:
        inv = tuple((p,1-z) for p,z in a)
        if inv not in inputs:
            raise ValueError(f"Missing conjugate for {a}")
    intervals = {k:(Fraction(str(v['B_lower'])),Fraction(str(v['B_upper']))) for k,v in data.items()}
    for lo,hi in intervals.values():
        if not 0 < lo <= hi:
            raise ValueError("Invalid positive-weight interval")
    trivial = frozenset({ONE})
    # Every element of a qualifying group generates a qualifying cyclic
    # subgroup. Test each of those once, retaining just one generator per
    # distinct cyclic subgroup to eliminate impossible or duplicate work.
    generators = []
    cyclic_seen = set()
    for a in ranking:
        C = generated(trivial,a)
        if C in cyclic_seen or not C <= inputs:
            continue
        cyclic_seen.add(C)
        if sum(intervals[k][0] for k in C) >= 2:
            continue
        generators.append(a)
    queue = [trivial]
    visited = {trivial}
    fields = []
    margins = []
    while queue:
        H = queue.pop()
        lo = sum(intervals[k][0] for k in H)
        hi = sum(intervals[k][1] for k in H)
        if lo >= 2:
            margins.append(float(lo-2))
            continue
        if hi >= 2:
            raise ValueError(f"Inconclusive at {H}")
        margins.append(float(2-hi))
        basis = []
        span = trivial
        for a in sorted(H-{ONE},key=by_size):
            if a not in span:
                basis.append(a)
                span = generated(span,a)
        assert span==H
        field = {"degree":len(H),"conductor":lcm(*(int(data[k]["q"]) for k in H)),
                 "group_invariant_factors":invariant_factors(H),
                 "quadratic_subfield_discriminants":sorted(int(data[k]["d"]) for k in H if order(k)==2),
                 "character_group_generators":[encode(k) for k in basis],
                 "B_field_lower":str(lo),"B_field_upper":str(hi)}
        fields.append(field)
        for a in generators:
            if a in H:
                continue
            G = generated(H,a)
            if G in visited:
                continue
            if G <= inputs:
                visited.add(G)
                queue.append(G)
    out = {"quadratic_candidate_count":len(quad['characters']),"nonreal_candidate_count":len(comp),
           "total_field_count":len(fields),
           "counts_by_degree":dict(sorted(Counter(f['degree'] for f in fields).items())),
           "counts_by_abelian_group":dict(sorted(Counter(str(f["group_invariant_factors"]) for f in fields).items())),
           "smallest_certified_threshold_margin_among_tested_groups_approx":min(margins),
           "fields":sorted(fields,key=lambda x:(x['degree'],x['conductor'],x['character_group_generators']))}
    print(json.dumps(out,indent=2))

if __name__ == "__main__":
    main()
