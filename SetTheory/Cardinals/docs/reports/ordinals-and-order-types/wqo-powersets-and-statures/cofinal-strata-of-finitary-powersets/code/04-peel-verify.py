"""Deterministic checks of finite reductions and two ordinal algorithms.

These tests are NOT a formal verification of the transfinite theorem.
Run from any working directory: python code/verify.py
"""
from __future__ import annotations
import itertools
import json
import platform
from pathlib import Path
from ordinals import Ordinal as O, ZERO, ONE, OMEGA
from persistent_height import (System, antichains, bits, closure, hoare_states,
                               pure_frontier_system, general_ordinal_system, solve)

ROOT = Path(__file__).resolve().parents[1]
COUNTS: dict[str, int] = {}

def check(condition: bool, category: str) -> None:
    if not condition:
        raise AssertionError(category)
    COUNTS[category] = COUNTS.get(category, 0) + 1


def posets(n: int):
    """All transitive subrelations of the natural label order, repetitions of
    isomorphism types allowed. Not all labelled posets, nor unlabelled counts.
    """
    pairs = list(itertools.combinations(range(n), 2))
    for mask in range(1 << len(pairs)):
        le = [1 << i for i in range(n)]
        for k, (i, j) in enumerate(pairs):
            if mask >> k & 1:
                le[i] |= 1 << j
        if all(not (le[j] & ~le[i]) for i in range(n) for j in bits(le[i])):
            yield le


def compare_algorithms(s: System, category: str, exhaustive: bool = True):
    s.validate()
    a, path = s.height_dp(False)
    b, _ = s.height_peeling()
    check(a == b, category + '_dp_vs_peeling')
    check(a == s.path_score(path), category + '_certificate')
    if exhaustive:
        check(a == s.height_exhaustive(), category + '_all_paths')
    return a


def test_arithmetic():
    # Independent coefficient-array ordinal addition below omega^4.
    arrays = list(itertools.product(range(3), repeat=4))
    def encode(a):
        return O(tuple((O.nat(k), a[k]) for k in range(3, -1, -1) if a[k]))
    for a in arrays:
        x = encode(a)
        check(O.parse(x.json()) == x, 'arithmetic_roundtrip')
        for b in arrays:
            y = encode(b)
            c = list(a)
            if any(b):
                k = max(i for i in range(4) if b[i])
                for j in range(k):
                    c[j] = b[j]
                c[k] += b[k]
            check(x + y == encode(c), 'arithmetic_ordinary_addition')
            check(x.natural_sum(y) == encode([a[i] + b[i] for i in range(4)]),
                  'arithmetic_natural_sum')
            check((x < y) == (tuple(reversed(a)) < tuple(reversed(b))), 'arithmetic_order')
    w2 = O.power(O.nat(2))
    womega = O.power(OMEGA)
    check(OMEGA + w2 == w2, 'hereditary_arithmetic')
    check(womega + w2 + womega == womega.right_times(2), 'hereditary_arithmetic')
    check(O.parse(womega.json()) == womega, 'hereditary_arithmetic')
    check(OMEGA.right_times(17) == O(((ONE,17),)), 'hereditary_arithmetic')


def test_frontiers():
    census = {}
    for n in range(1, 7):
        count = 0
        for le in posets(n):
            count += 1
            weights = itertools.product((1,2,3), repeat=n) if n <= 4 else [(1,)*n]
            for exponents in weights:
                caps = [O.power(O.nat(e)) for e in exponents]
                s, _ = pure_frontier_system(le, caps)
                height = compare_algorithms(s, 'pure_weighted' if n <= 4 else 'pure_uniform', n <= 5)
                if len(set(exponents)) == 1:
                    d = [1]*len(s.le)
                    from persistent_height import topological
                    for j in topological(s.le):
                        d[j] = max([1] + [d[i]+1 for i in range(len(d))
                                          if i != j and s.le[i] >> j & 1])
                    check(height == caps[0].right_times(max(d)), 'uniform_repository_formula')
                if n <= 4:
                    full, _, _ = general_ordinal_system(le, caps)
                    full_h, _ = full.height_dp()
                    check(full_h == height, 'pure_maximal_vs_all_frontiers')
        census[n] = count
    return census


def test_general_systems():
    # Exhaust all two-label active-set assignments on state posets through 4.
    # No-resurrection is checked before evaluating the theorem.
    accepted = rejected = 0
    capacities = {0: OMEGA, 1: O.power(O.nat(2))}
    for n in range(0,5):
        for le in posets(n):
            for active in itertools.product(range(4), repeat=n):
                s = System(le, list(active), capacities)
                try:
                    s.validate()
                except ValueError:
                    rejected += 1
                    continue
                accepted += 1
                compare_algorithms(s, 'abstract_system')
    return {'accepted': accepted, 'rejected_no_resurrection': rejected}


def structural_test(le, lengths):
    """Independently build all downsets of an actual finite lex sum and check
    its all-antichain encoding. This tests the representation, not the
    infinite-capacity height theorem via finite approximation.
    """
    points = [(q,k) for q, n in enumerate(lengths) for k in range(n)]
    n = len(points)
    down = []
    for q,k in points:
        mask = 0
        for i,(r,l) in enumerate(points):
            if (r == q and l <= k) or (r != q and le[r] >> q & 1):
                mask |= 1 << i
        down.append(mask)
    actual = [mask for mask in range(1 << n)
              if all(not (down[i] & ~mask) for i in bits(mask))]
    fronts = antichains(le)
    encoded = []
    for front in fronts:
        indices = list(bits(front))
        for values in itertools.product(*(range(lengths[q]) for q in indices)):
            coords = dict(zip(indices, values))
            mask = 0
            for q,k in coords.items():
                mask |= down[points.index((q,k))]
            encoded.append((front,coords,mask))
    check(sorted(m for _,_,m in encoded) == actual, 'finite_representation_bijection')
    for a,x,m in encoded:
        for b,y,nmask in encoded:
            relation = all(le[q] & b for q in bits(a)) and all(x[q] <= y[q] for q in bits(a & b))
            check(relation == (m & ~nmask == 0), 'finite_representation_order_pairs')


def test_finite_structure():
    for n in range(5):
        for le in posets(n):
            lengths_list = itertools.product((1,2), repeat=n) if n <=3 else [(1,)*n,(2,)*n]
            for lengths in lengths_list:
                structural_test(le, lengths)
            for lengths in itertools.product((0,1,2), repeat=n):
                fibers = [O.nat(k) for k in lengths]
                s,_,_ = general_ordinal_system(le, fibers)
                h,_ = s.height_dp()
                check(h == O.nat(sum(lengths)+1), 'finite_ordinal_height')


def test_examples():
    examples = {
        'empty': ({'n':0,'edges':[],'fibers':[]}, ONE),
        'persistent_large_coordinate': (json.loads((ROOT/'examples/persistent_large_coordinate.json').read_text()), O.power(O.nat(2))),
        'weighted_N': (json.loads((ROOT/'examples/weighted_N.json').read_text()), O.power(O.nat(3))+O.power(O.nat(2))),
        'successor_product': (json.loads((ROOT/'examples/successor_product.json').read_text()), OMEGA.right_times(2)+ONE),
        'mixed_successor_product': ({'n':2,'edges':[],'fibers':[[[2,1],[0,1]],[[1,1],[0,1]]]}, O.power(O.nat(2))+OMEGA+ONE),
        'single_impure': ({'n':1,'edges':[],'fibers':[[[2,1],[1,2],[0,3]]]}, O.power(O.nat(2))+OMEGA.right_times(2)+O.nat(3)),
        'uniform_N': ({'n':4,'edges':[[0,2],[1,2],[1,3]],'fibers':[[[1,1]]]*4,'mode':'pure'}, OMEGA.right_times(3)),
        'transfinite_exponents': ({'n':3,'edges':[[1,2]],'fibers':[[[[[1,1]],1]],[[1,1]],[[1,1]]],'mode':'pure'}, O.power(OMEGA)),
        'N_high_b': ({'n':4,'edges':[[0,2],[1,2],[1,3]],'fibers':[[[1,1]],[[2,1]],[[1,1]],[[1,1]]],'mode':'pure'}, O.power(O.nat(2))+OMEGA.right_times(2)),
        'N_high_a': ({'n':4,'edges':[[0,2],[1,2],[1,3]],'fibers':[[[2,1]],[[1,1]],[[1,1]],[[1,1]]],'mode':'pure'}, O.power(O.nat(2))+OMEGA),
    }
    results={}
    for name,(data,expected) in examples.items():
        result=solve(data)
        check(O.parse(result['height_cnf']) == expected, 'worked_example')
        results[name]=result
        (ROOT/'examples'/f'{name}.json').write_text(json.dumps(data,indent=2)+'\n')
    (ROOT/'data'/'examples_results.json').write_text(json.dumps(results,indent=2)+'\n')
    # Bad inputs fail loudly, rather than silently changing the hypothesis.
    bad=System(closure(3,[(0,1),(1,2)]),[1,0,1],{0:OMEGA})
    try:
        bad.validate()
    except ValueError:
        check(True,'invalid_input_rejection')
    else:
        check(False,'invalid_input_rejection')
    for value in ([[1,0]], [[0,1],[1,1]], -1):
        try:
            O.parse(value)
        except ValueError:
            check(True,'invalid_input_rejection')
        else:
            check(False,'invalid_input_rejection')
    return {name:r['height'] for name,r in results.items()}


def main():
    test_arithmetic()
    print('Ordinal arithmetic checks passed.', flush=True)
    census=test_frontiers()
    print('Frontier checks passed.', flush=True)
    abstract=test_general_systems()
    print('Abstract persistent systems passed.', flush=True)
    test_finite_structure()
    print('Finite representation checks passed.', flush=True)
    examples=test_examples()
    report={'status':'PASS','python':platform.python_version(),
            'naturally_labelled_poset_census':census,'abstract_system_cases':abstract,
            'checks_by_category':COUNTS,'total_assertions':sum(COUNTS.values()),
            'worked_examples':examples,
            'scope':'Finite structural and algorithmic checks; not proof-assistant verification or numerical evaluation of infinite ranks.'}
    (ROOT/'data'/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
