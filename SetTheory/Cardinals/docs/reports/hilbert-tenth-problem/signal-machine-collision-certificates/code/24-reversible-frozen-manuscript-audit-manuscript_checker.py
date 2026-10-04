#!/usr/bin/env python3
"""New small manuscript-transcription check; imports no candidate/audit code."""
import hashlib
import json
from pathlib import Path
from random import Random

ROWS = {
    'A': [('AR', {0, 1}, {0, 2}, -4, 6),
          ('AL', {0, 4}, {0, 3}, -4, 8),
          ('AC', {0, 1, 6}, {-1, 2, 7}, -5, 8)],
    'B': [('BR', {0, 2}, {1, 2}, -4, 6),
          ('BL', {0, 3}, {-1, 3}, -5, 7),
          ('BC', {-5, 0, 3}, {-5, 0, 1}, -5, 8)]}

def need(ok, context):
    if not ok:
        raise RuntimeError(context)

def raw(c, block):
    result = {}
    for label, e0, e1, lo, hi in ROWS[block]:
        # Any matching nonempty endpoint contains an occupied site.
        for x in {p - q for p in c for q in e0 | e1}:
            seen = {p-x for p in c if x+lo <= p <= x+hi}
            if seen == e0 or seen == e1:
                result[(label, x)] = {x+q for q in e0 ^ e1}
    return result

def block(c, name):
    keys = raw(c, name)
    chosen = {}
    for key, delta in keys.items():
        if any(other != key and abs(other[1]-key[1]) <= 30 for other in keys):
            continue
        if set(raw(c ^ delta, name)) == set(keys):
            chosen[key] = delta
    result = set(c)
    for delta in chosen.values():
        result ^= delta
    return result, set(chosen)

def step(c):
    return block(block(c, 'A')[0], 'B')[0]

def inverse(c):
    return block(block(c, 'B')[0], 'A')[0]

def phase(d, s):
    if s <= d-11:
        return {0, 5+s, 6+s, d}
    return {0, 2*d-18-s, 2*d-14-s, d+1}

def halfstep(c, name, key, expected):
    need(set(raw(c, name)) == {key}, ('unique-before', c, name, key))
    out, selected = block(c, name)
    need(selected == {key}, ('selected', c, name, key))
    need(out == expected, ('output', c, name, expected))
    need(set(raw(out, name)) == {key}, ('unique-after', out, name, key))
    need(block(out, name)[0] == c, ('involution', c, name))
    return out

def check_step(d, s):
    c = phase(d, s)
    if s < d-11:
        p = 5+s
        middle = halfstep(c, 'A', ('AR', p), {0, p, p+2, d})
        out = halfstep(middle, 'B', ('BR', p), {0, p+1, p+2, d})
    elif s == d-11:
        middle = halfstep(c, 'A', ('AC', d-6), {0, d-7, d-4, d+1})
        out = halfstep(middle, 'B', ('BL', d-7), {0, d-8, d-4, d+1})
    else:
        q = 2*d-18-s
        middle = halfstep(c, 'A', ('AL', q), {0, q, q+3, d+1})
        if q == 5:
            out = halfstep(middle, 'B', ('BC', 5), {0, 5, 6, d+1})
        else:
            out = halfstep(middle, 'B', ('BL', q), {0, q-1, q+3, d+1})
    expected = {0, 5, 6, d+1} if s == 2*d-23 else phase(d, s+1)
    need(out == expected, ('next-phase', d, s))
    need(inverse(out) == c, ('inverse', d, s))
    return 1

def main():
    phase_steps = 0
    for d in range(13, 54):
        for s in range(2*d-22):
            phase_steps += check_step(d, s)
            c = phase(d, s)
            need((c & set(range(7)) == {0, 5, 6}) == (s == 0), ('hit', d, s))
            need((c & set(range(6)) == {0}) == (1 <= s <= 2*d-24), ('dense-hit', d, s))
    large_steps = 0
    for d in [10**6+13, 10**30+1, 10**100]:
        for s in sorted({0, 1, d-12, d-11, d-10, 2*d-24, 2*d-23}):
            large_steps += check_step(d, s)
    rng = Random(4904)
    generic = [set(), {-8,-5,0,1}, {-8,-5,0,1,70,71}]
    generic += [set(rng.sample(range(-120, 121), rng.randrange(65))) for _ in range(300)]
    for c in generic:
        for name in ('A', 'B'):
            out, chosen = block(c, name)
            need(len(out) == len(c), ('mass', c, name))
            need(set(raw(out, name)) == set(raw(c, name)), ('raw-preservation', c, name))
            need(block(out, name) == (c, chosen), ('full-selected-involution', c, name))
        need(inverse(step(c)) == c and step(inverse(c)) == c, ('inverse-pair', c))
    need(block({-8,-5,0,1}, 'A')[0] == {-8,-5,0,1}, 'birth rejection')
    need(block({-8,-5,0,1,70,71}, 'A')[0] == {-8,-5,0,1,70,72}, 'mixed statuses')
    result = {'PASS': True, 'cycle_parameters': '13..53 inclusive',
              'complete_steps_and_both_halfsteps': phase_steps,
              'large_coordinate_steps': large_steps,
              'generic_finite_supports': len(generic),
              'dense_observation': '100000 hits at s=1..L_D-2',
              'source_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'scope': 'Finite supplementary tests; full-shift and unbounded conclusions rely on reviewed proofs.'}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
