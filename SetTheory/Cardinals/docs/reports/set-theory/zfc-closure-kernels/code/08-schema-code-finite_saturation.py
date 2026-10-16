#!/usr/bin/env python3
"""Finite regressions for the raw PSC interpretation, not a proof of the theory.

Exhaust every membership graph on one, two, or three labelled objects.
All tests below are exact finite statements.  In particular, no finite
structure is used as evidence that the unrestricted schema is consistent.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path


def members(mask: int, n: int):
    return [i for i in range(n) if mask >> i & 1]


def inspect(n: int, graph: int):
    cols = [sum(((graph >> (x*n+y)) & 1) << x for x in range(n)) for y in range(n)]
    rows = [sum(((graph >> (x*n+y)) & 1) << y for y in range(n)) for x in range(n)]
    def sub(x, y): return cols[x] & ~cols[y] == 0
    def d(x, y): return cols[x] == cols[y]
    def e(x, y): return d(x, y) and rows[x] == rows[y]
    def mem(x, y): return bool(cols[y] >> x & 1)
    trans = [all(sub(x, t) for x in members(cols[t], n)) for t in range(n)]
    sat = [all(not mem(x, y) or not d(x, z) or mem(z, y)
               for x in range(n) for z in range(n)) for y in range(n)]
    h = [sat[y] and any(trans[t] and sub(y, t) and
         all(sat[z] for z in members(cols[t], n)) for t in range(n)) for y in range(n)]
    hmask = sum(int(h[x]) << x for x in range(n))
    counts = dict(full_profile_atomic_congruence=0, hereditary_profile_invariance=0,
                  hereditary_downward=0, quotient_congruence=0, quotient_extensionality=0,
                  subset_absoluteness=0, conditional_purity_closure=0)
    for x in range(n):
        for y in range(n):
            if d(x,y):
                assert h[x] == h[y]
                counts['hereditary_profile_invariance'] += 1
            if h[y] and mem(x,y):
                assert h[x]
                counts['hereditary_downward'] += 1
            if h[x] and h[y]:
                same_on_h = all(mem(z,x) == mem(z,y) for z in range(n) if h[z])
                assert not same_on_h or d(x,y)
                counts['quotient_extensionality'] += 1
                sub_on_h = all(not mem(z,x) or mem(z,y) for z in range(n) if h[z])
                assert sub_on_h == sub(x,y)
                counts['subset_absoluteness'] += 1
            for z in range(n):
                if h[z] and d(x,y):
                    assert mem(x,z) == mem(y,z)
                    counts['quotient_congruence'] += 1
                if e(x,y):
                    assert mem(x,z) == mem(y,z) and mem(z,x) == mem(z,y)
                    counts['full_profile_atomic_congruence'] += 1
    for y in range(n):
        if sat[y] and all(h[x] for x in members(cols[y], n)):
            for t in range(n):
                if trans[t] and sub(y,t) and (cols[t] & hmask) in cols:
                    assert h[y]
                    counts['conditional_purity_closure'] += 1
    # These are necessary constant-matrix PSC consequences. Each local bound
    # is immediate: the empty relation is bounded by any object; y subset a
    # is bounded by a. An exact constant fiber is forced by the reflexive seed.
    if 0 not in cols:
        reject = dict(instance='empty_constant', parameter=None)
    else:
        reject = None
        for a in range(n):
            power_extension = sum(int(sub(y,a)) << y for y in range(n))
            if power_extension not in cols:
                reject = dict(instance='subset_constant', parameter=a,
                              missing_extension=power_extension)
                break
    return counts, reject, cols, h


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('finite_saturation_results.json'))
    args = parser.parse_args()
    records, totals, counterexamples = [], {}, []
    for n in (1,2,3):
        rejections = dict(empty_constant=0, subset_constant=0, not_rejected=0)
        nonempty_h = 0
        for graph in range(1 << (n*n)):
            counts, reject, cols, h = inspect(n,graph)
            for name,value in counts.items(): totals[name] = totals.get(name,0)+value
            nonempty_h += any(h)
            rejections['not_rejected' if reject is None else reject['instance']] += 1
            if reject is None: counterexamples.append(dict(n=n,graph=graph))
        records.append(dict(domain_size=n, structures=1 << (n*n),
                            structures_with_nonempty_H=nonempty_h, rejections=rejections))
    # A small explicit illustration: 0 and 1 have empty predecessor profiles,
    # but only 0 belongs to object 2. H discards object 2, not 0 and 1.
    _, _, cols, h = inspect(3, 1 << 2)
    assert cols == [0,0,1] and h == [True,True,False]
    assert not counterexamples
    result = dict(scope='Finite algebra regressions and explicit necessary-instance refutations only; not a Lean proof or consistency test.',
                  structures=sum(r['structures'] for r in records), records=records,
                  exact_assertion_counts=totals,
                  raw_profile_failure_example=dict(n=3,edges=[[0,2]],columns=cols,H=h),
                  all_structures_rejected_by_constant_PSC_instances=True)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__ == '__main__':
    main()
