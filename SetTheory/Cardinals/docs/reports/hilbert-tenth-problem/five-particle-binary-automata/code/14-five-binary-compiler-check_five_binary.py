"""Finite regression evidence, supplementary to the all-input proof."""
import hashlib
import itertools
import json
import random
from pathlib import Path
from five_binary import Machine, BinaryCA


def source_fixture():
    return Machine({
        "a": ["ADD", 0, "b"], "b": ["ADD", 1, "c"],
        "c": ["SUB", 0, "d", "e"], "d": ["SUB", 1, "e", "a"],
        "e": ["SUB", 1, "c", "f"], "f": ["NOP", "HALT"],
    }, "a", "HALT")


def run():
    m = source_fixture()
    ca = BinaryCA(m)
    counts = dict(macro_cases=0, microsteps=0, source_steps=0,
                  malformed_cases=0, local_sites=0, local_boundary_cases=0)
    for q in ca.states:
        for a, b in itertools.product(range(6), repeat=2):
            x = ca.encode(q, a, b)
            expected = ca.encode(*m.step(q, a, b))
            t = ca.duration(q, a, b)
            for _ in range(t):
                x = ca.step(x)
                assert len(x) == 5
            assert x == expected, (q, a, b, t, x, expected)
            counts["macro_cases"] += 1
            counts["microsteps"] += t
    # Long instruction mixtures include both directions, same-side repeats,
    # positive decrement down to zero, a zero branch, a NOOP, and halting.
    for a, b in itertools.product(range(6), repeat=2):
        q = m.entry
        x = ca.encode(q, a, b)
        for _ in range(40):
            assert x == ca.encode(q, a, b)
            if q == m.halt:
                assert ca.step(x) == x
                break
            t = ca.duration(q, a, b)
            for _ in range(t):
                x = ca.step(x)
            q, a, b = m.step(q, a, b)
            counts["source_steps"] += 1
            counts["microsteps"] += t
        else:
            assert False, "fixture should halt"
    rng = random.Random(9031)
    for _ in range(1200):
        # Mix dense/invalid components, multiple heads, and remote sensors.
        x = {rng.randrange(-2*ca.radius, 2*ca.radius+1) for _ in range(rng.randrange(35))}
        if rng.randrange(2):
            shift = rng.randrange(-ca.K, ca.K)
            x |= {shift, shift+ca.C, shift+ca.C+rng.randrange(1, ca.D+1)}
        y = ca.step(x)
        assert len(x) == len(y)
        shift = rng.randrange(-100, 101)
        assert ca.step({z+shift for z in x}) == {z+shift for z in y}
        centers = {0} | x | y
        for c in centers:
            window = {z-c for z in x if abs(z-c) <= ca.radius}
            assert ca.local(window) == int(c in y), (x, c)
            counts["local_sites"] += 1
        counts["malformed_cases"] += 1
    # Explicit long connected components cross both truncation boundaries.
    for d in (1, ca.D, ca.C, ca.K):
        x = set(range(-2*ca.radius, 2*ca.radius+1, d))
        for c in (0, min(x), max(x), min(x)+ca.K, max(x)-ca.K):
            y = ca.step(x)
            assert ca.local({z-c for z in x if abs(z-c) <= ca.radius}) == int(c in y)
            counts["local_boundary_cases"] += 1
    p = Path(__file__).parent/'source-replay/source/literal2.json'
    data = p.read_bytes()
    expected_hash = '85e16b44828f2f3d4ad6d0805dcc9e9922893a6d286874f2018d6a33af864b00'
    assert hashlib.sha256(data).hexdigest() == expected_hash
    raw = json.loads(data)
    uni = BinaryCA(Machine(raw['rows'], raw['entry'], raw['halt']))
    # Structural checks use the actual literal table.  No claim is made here
    # to replay its astronomically large universal computations.
    for q in uni.moving:
        for a,b in ((0,0),(0,1),(1,0),(1,1)):
            assert uni.duration(q,a,b) >= 1
    out = dict(status='passed', checks=counts, fixture=ca.ledger(),
               universal_source_sha256=expected_hash,
               universal=uni.ledger(),
               universal_source_operation_counts={op:sum(r[0]==op for r in raw['rows'].values()) for op in ('ADD','SUB')})
    Path(__file__).with_name('checks.json').write_text(json.dumps(out, indent=2)+'\n')
    print(json.dumps(out, indent=2))


if __name__ == '__main__':
    run()
