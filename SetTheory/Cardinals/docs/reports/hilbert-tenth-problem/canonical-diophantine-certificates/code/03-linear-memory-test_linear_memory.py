#!/usr/bin/env python3
"""Reproducible checks for the deterministic large-base memory compiler."""
from __future__ import annotations
from collections import Counter
import itertools
import json
from math import prod
from pathlib import Path
import random
import time
from canonical_memory import Event, valid_log
from linear_memory import compile_linear_log


def check_fingerprints():
    """Check injectivity on multisets, including repetitions and zero."""
    cases = 0
    for c in range(2, 7):
        for length in range(1, 5):
            beta = c**length+1
            seen = {}
            for row in itertools.combinations_with_replacement(range(c), length):
                fingerprint = prod(beta+x for x in row)
                assert fingerprint not in seen, (c, length, seen[fingerprint], row)
                seen[fingerprint] = row
                cases += 1
    return cases


def check_system(events):
    s = compile_linear_log(events)
    length = len(events)
    assert s.roles.count('witness') == 24*length
    assert len(s.residuals) == 22*length+1
    assert (not s.violations()) == valid_log(events)
    assert all(p.degree <= 2 and len(p.terms) <= 8 for p in s.residuals)
    if length:
        d = s.values[s.names.index('radix.D')]
        upper = 2**length*d**(4*length*length)
        assert all(v <= upper for v, role in zip(s.values, s.roles) if role == 'witness')
        expected = [(e.address+1, (length+1)*(e.address+1)+t, e.write, e.value)
                    for t, e in enumerate(events)]
        actual = [tuple(s.value(p) for p in row) for row in s.sorted_records]
        assert actual == sorted(expected, key=lambda row: row[1])
    return s



def check_coherent_forgery():
    """Recompute all derived output data after forging one sorted record.

    All events are writes, so the forged history itself is memory-consistent.
    The exact product identity alone must detect the changed record multiset.
    """
    s = check_system([Event(2,1,9), Event(7,1,4), Event(9,1,3)])
    values = list(s.values)
    ids = {name: i for i, name in enumerate(s.names)}
    def get(name):
        return values[ids[name]]
    def put(name, value):
        values[ids[name]] = value
    fields = ('alpha','key','w','v')
    for field in fields:
        put('sorted0.'+field, get('sorted1.'+field))
    d = get('radix.D')
    for i in range(3):
        for j, field in enumerate(fields):
            put(f'sorted{i}.bound{j}', d-get(f'sorted{i}.{field}')-1)
        h1 = get(f'sorted{i}.v')*d+get(f'sorted{i}.w')
        h2 = h1*d+get(f'sorted{i}.key')
        code = h2*d+get(f'sorted{i}.alpha')
        for j, value in enumerate((h1,h2,code)):
            put(f'pack.output{i}.stage{j}', value)
    product = 1
    for i in range(3):
        product *= get('radix.beta')+get(f'pack.output{i}.stage2')
        put(f'product.output{i}', product)
    for i in range(1,3):
        put(f'order{i}.gap', get(f'sorted{i}.key')-get(f'sorted{i-1}.key'))
        delta = get(f'sorted{i}.alpha')-get(f'sorted{i-1}.alpha')
        put(f'memory{i}.same', int(delta == 0))
        put(f'memory{i}.gap_minus_one', max(0,delta-1))
        put(f'memory{i}.previous_value', get(f'sorted{i-1}.v') if delta == 0 else 0)
    assert s.violations(values) == ['product.equality']
    return 'rejected solely by product.equality'

def main():
    start = time.monotonic()
    fingerprint_cases = check_fingerprints()
    coherent_forgery = check_coherent_forgery()
    alphabet = [Event(a,w,v) for a,w,v in itertools.product(range(2), repeat=3)]
    cases, valid = 0, 0
    for length in range(4):
        for row in itertools.product(alphabet, repeat=length):
            check_system(list(row))
            cases += 1
            valid += int(valid_log(list(row)))
    # Write flags greater than one must not be silently accepted.
    invalid_flags = 0
    for w in range(2, 8):
        check_system([Event(0,w,0)])
        invalid_flags += 1
    rng = random.Random(240922)
    random_cases, corruptions = 0, 0
    for _ in range(40):
        memory, events = {}, []
        addresses = [rng.getrandbits(60) for _ in range(4)]
        for _ in range(rng.randrange(1, 13)):
            a, w = rng.choice(addresses), rng.randrange(2)
            v = rng.getrandbits(80) if w else memory.get(a,0)
            events.append(Event(a,w,v))
            if w:
                memory[a] = v
        check_system(events)
        random_cases += 1
        reads = [i for i, e in enumerate(events) if not e.write]
        if reads:
            i = rng.choice(reads)
            broken = list(events)
            e = broken[i]
            broken[i] = Event(e.address,0,e.value+1)
            check_system(broken)
            corruptions += 1
    example = [Event(7,0,0), Event(2,1,9), Event(7,1,4), Event(2,0,9)]
    s = check_system(example)
    mutations = 0
    for i, role in enumerate(s.roles):
        if role == 'witness':
            changed = list(s.values)
            changed[i] += 1
            assert s.violations(changed), s.names[i]
            mutations += 1
    p = s.expanded_polynomial()
    assert p.degree == 4 and p.evaluate(s.values) == 0
    for _ in range(20):
        xs = [rng.randrange(5) for _ in s.values]
        assert p.evaluate(xs) == s.energy(xs)
    # The symbolic formula must not change with numerical parameter values.
    same_length = compile_linear_log([Event(0,0,0)]*4)
    assert s.names == same_length.names
    assert [f.terms for f in s.residuals] == [f.terms for f in same_length.residuals]
    root = Path(__file__).resolve().parents[1]
    dest = root/'artifacts'/'linear_example'
    s.export(dest, expanded=True)
    (dest/'events.json').write_text(json.dumps([[e.address,e.write,e.value] for e in example], indent=2)+'\n')
    results = dict(fingerprint_multisets=fingerprint_cases,
                   coherent_multiset_forgery=coherent_forgery,
                   exhaustive_logs=dict(cases=cases,valid=valid,invalid=cases-valid),
                   invalid_write_flags=invalid_flags,
                   large_integer_logs=random_cases, corrupted_reads=corruptions,
                   witness_mutations_rejected=mutations,
                   expanded_degree=p.degree, expanded_monomials=len(p.terms),
                   expansion_identity_tests=20,
                   parameter_independent_polynomial=True,
                   example=s.summary(), seconds=round(time.monotonic()-start,3),status='PASS')
    (root/'artifacts'/'linear_test_results.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__ == '__main__':
    main()
