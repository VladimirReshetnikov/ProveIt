#!/usr/bin/env python3
"""Deterministic regression/exhaustion checks; not a substitute for the proofs."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
import random
import time
from canonical_memory import Event, compile_log, valid_log, bitonic_network


def check_comparison():
    cases = 0
    for x in range(9):
        for y in range(9):
            solutions = [(b, d) for b in range(4) for d in range(12)
                         if b * (b - 1) == 0 and y - x - (2*b-1)*d - b + 1 == 0]
            expected = (1, y-x) if x <= y else (0, x-y-1)
            assert solutions == [expected], (x, y, solutions)
            cases += 1
    return cases


def check_zero():
    for delta in range(21):
        solutions = [(z, h) for z in range(4) for h in range(23)
                     if z * (z-1) == 0 and delta + (2*z-1)*h + z - 1 == 0]
        assert solutions == [(1, 0) if delta == 0 else (0, delta-1)]
    return 21


def check_networks():
    cases = 0
    for n in (1, 2, 4, 8):
        network = list(bitonic_network(n))
        k = n.bit_length()-1
        assert len(network) == n*k*(k+1)//4
        for perm in itertools.permutations(range(n)):
            xs = list(perm)
            for i, j, asc in network:
                if (xs[i] > xs[j]) == asc:
                    xs[i], xs[j] = xs[j], xs[i]
            assert xs == list(range(n))
            cases += 1
    # Zero-one principle checks on a larger network, independently of distinctness.
    n = 16
    network = list(bitonic_network(n))
    for bits in itertools.product(range(2), repeat=n):
        xs = list(bits)
        for i, j, asc in network:
            if (xs[i] > xs[j]) == asc:
                xs[i], xs[j] = xs[j], xs[i]
        assert xs == sorted(bits)
        cases += 1
    return cases


def check_system(events):
    s = compile_log(events)
    l, n, c = len(events), s.padded_length, s.comparators
    assert s.roles.count('witness') == 10*c + 2*l + 3*(n-1)
    assert len(s.residuals) == 10*c + 3*l + 4*(n-1) + 1
    assert all(p.degree <= 2 for p in s.residuals)
    assert (not s.violations()) == valid_log(events)
    expected = [(e.address+1, (n+1)*(e.address+1)+t, e.write, e.value)
                for t,e in enumerate(events)]
    expected += [(0,t,1,0) for t in range(l,n)]
    actual = [tuple(s.value(p) for p in row) for row in s.sorted_records]
    assert actual == sorted(expected, key=lambda row: row[1])
    a = max((e.address for e in events), default=0)
    v = max((e.value for e in events), default=0)
    h = max(1, v, (n+1)*(a+1)+n-1)
    assert all(x <= h for x, role in zip(s.values,s.roles) if role == 'witness')
    return s


def check_exhaustive_logs():
    alphabet = [Event(a,w,v) for a,w,v in itertools.product(range(2), repeat=3)]
    count, good = 0, 0
    for length in range(4):
        for row in itertools.product(alphabet, repeat=length):
            check_system(list(row))
            count += 1
            good += int(valid_log(list(row)))
    return dict(cases=count, valid=good, invalid=count-good)


def check_random_logs():
    rng = random.Random(20260930)
    count, invalid = 0, 0
    for _ in range(150):
        length = rng.randrange(1, 25)
        addresses = [rng.getrandbits(rng.choice([0,4,32,160])) for _ in range(6)]
        memory, events = {}, []
        for _ in range(length):
            a = rng.choice(addresses)
            w = rng.randrange(2)
            v = rng.getrandbits(rng.choice([0,8,64,200])) if w else memory.get(a,0)
            events.append(Event(a,w,v))
            if w:
                memory[a] = v
        check_system(events)
        count += 1
        reads = [i for i,e in enumerate(events) if not e.write]
        if reads:
            i = rng.choice(reads)
            broken = list(events)
            e = broken[i]
            broken[i] = Event(e.address, 0, e.value+1)
            assert not valid_log(broken)
            check_system(broken)
            invalid += 1
    return dict(valid=count, deliberately_invalid=invalid)


def check_mutations_and_expansion():
    events = [Event(7,0,0), Event(2,1,9), Event(7,1,4),
              Event(2,0,9), Event(7,0,4), Event(2,1,0)]
    s = check_system(events)
    count = 0
    for i, role in enumerate(s.roles):
        if role == 'witness':
            values = list(s.values)
            values[i] += 1
            assert s.violations(values), s.names[i]
            count += 1
    # Explicit quartic coefficient expansion on a four-event symbolic log.
    small = check_system(events[:4])
    p = small.expanded_polynomial()
    assert p.degree == 4
    assert p.evaluate(small.values) == small.energy() == 0
    rng = random.Random(81)
    for _ in range(20):
        values = [rng.randrange(4) for _ in small.values]
        assert p.evaluate(values) == small.energy(values)
    destination = Path(__file__).resolve().parents[1] / 'artifacts' / 'example'
    small.export(destination, expanded=True)
    (destination/'events.json').write_text(json.dumps(
        [[e.address,e.write,e.value] for e in events[:4]], indent=2)+'\n')
    return dict(witness_mutations_rejected=count, expanded_polynomial_terms=len(p.terms),
                expanded_polynomial_degree=p.degree, expansion_identity_tests=20,
                six_event_summary=s.summary(), four_event_summary=small.summary())


def check_coin_weights():
    # Stop at the first 1; acceptance by horizon T has probability 1-2^(-T).
    cases = []
    for t in range(1, 13):
        weights = [2**(t-halt_time) for halt_time in range(1,t+1)]
        assert sum(weights) == 2**t-1
        cases.append(dict(horizon=t, accepting_paths=t, weight_sum=sum(weights), denominator=2**t))
    return cases


def main():
    start = time.monotonic()
    results = dict(comparator_input_pairs=check_comparison(), zero_input_cases=check_zero(),
                   sorting_network_tests=check_networks(), exhaustive_logs=check_exhaustive_logs(),
                   large_integer_logs=check_random_logs(),
                   mutation_and_expansion=check_mutations_and_expansion(),
                   probability_weights=check_coin_weights())
    results['seconds'] = round(time.monotonic()-start,3)
    results['status'] = 'PASS'
    out = Path(__file__).resolve().parents[1] / 'artifacts' / 'test_results.json'
    out.write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__ == '__main__':
    main()
