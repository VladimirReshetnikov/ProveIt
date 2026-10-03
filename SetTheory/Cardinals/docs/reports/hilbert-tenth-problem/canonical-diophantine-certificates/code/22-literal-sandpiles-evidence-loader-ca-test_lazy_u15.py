#!/usr/bin/env python3
"""Verification of the literal rule enumeration, TM simulation, and shutdown."""
from __future__ import annotations
from collections import Counter
import gzip
import hashlib
import json
from pathlib import Path
import random
from lazy_u15 import *

HERE = Path(__file__).resolve().parent


def require(condition, detail="verification failed"):
    if not condition:
        raise AssertionError(detail)

def main():
    pure = json.loads((HERE.parent / 'data' / 'u15_table.json').read_text())
    require(DELTA == {k: None if v is None else (v[0], 1 if v[1] == 'R' else -1, v[2]) for k, v in pure.items()}, 'test_lazy_u15.py: invariant at original line 17')
    saved_manifest = json.loads((HERE / 'manifest.json').read_text())
    require(json.loads(json.dumps(manifest())) == saved_manifest, 'test_lazy_u15.py: invariant at original line 20')
    with gzip.open(HERE / 'rules.jsonl.gz', 'rb') as f:
        content = f.read()
    require(hashlib.sha256(content).hexdigest() == saved_manifest['canonical_integer_rules_jsonl_sha256'], 'test_lazy_u15.py: invariant at original line 23')
    require(len(content.splitlines()) == 388146, 'test_lazy_u15.py: invariant at original line 24')
    engine = CompiledRules()
    require(sum(engine.counts.values()) == 388146, 'test_lazy_u15.py: invariant at original line 26')
    require(engine.step({}) == {}, 'test_lazy_u15.py: invariant at original line 27')
    require(engine.matching((LAZY,) * 5) == [], 'test_lazy_u15.py: invariant at original line 28')
    require(saved_manifest['input_occurrence_count_by_state_f_s'][str(HALT)] == 0, 'test_lazy_u15.py: invariant at original line 29')
    # Exact nearest-head-first pair grammar and seed placement.
    for ell in ('', '0', '1', '00110'):
        for right_word in ('', '0', '1', '101100'):
            require(parse_pair(serialize_pair(ell, right_word)) == (ell, right_word), 'test_lazy_u15.py: invariant at original line 33')
            pair_cells, pair_l, pair_r = initialize_pair(ell, right_word)
            require(pair_l == min(-3, -len(ell) - 1), 'test_lazy_u15.py: invariant at original line 35')
            require(pair_r == max(3, len(right_word) + 1), 'test_lazy_u15.py: invariant at original line 36')
            require(pair_cells[0] == head('A', 0), 'test_lazy_u15.py: invariant at original line 37')
            for i, bit in enumerate(ell):
                require(pair_cells[-i - 1] == int(bit), 'test_lazy_u15.py: invariant at original line 39')
            for i, bit in enumerate(right_word):
                require(pair_cells[i + 1] == int(bit), 'test_lazy_u15.py: invariant at original line 41')
            require(initialize_serialized_pair(serialize_pair(ell, right_word)) == (pair_cells, pair_l, pair_r), 'test_lazy_u15.py: invariant at original line 42')
    for invalid in ('', '1', '11', '1100', 'x'):
        try:
            parse_pair(invalid)
        except ValueError:
            pass
        else:
            raise AssertionError(('Invalid serialization accepted', invalid))
    cases = []
    # Each headed state and symbol, including an initially final head.
    for q in Q:
        for bit in (0, 1):
            cases.append((f'head_{q}{bit}', {-2: 1, 0: bit, 2: 1}, q, (-2, 2), 60))
    rng = random.Random(313)
    for i in range(25):
        a, b = -rng.randrange(1, 15), rng.randrange(1, 15)
        tape = {x: rng.randrange(2) for x in range(a, b + 1)}
        cases.append((f'random_{i}', tape, 'A', (a, b), 100))
    word = '01100001100111101000010100111001100001011'
    cases.append(('A_halt_T75_p_minus13', {i - 20: int(bit) for i, bit in enumerate(word)},
                  'A', (-20, 20), 100))
    # Long blank collars and immediate shutdown stress fronts independently.
    cases.append(('initial_halt_long_left', {-25: 1, 0: 1}, 'J', (-25, 2), 1))
    cases.append(('initial_halt_long_right', {0: 1, 25: 1}, 'J', (-2, 25), 1))
    total_updates = 0
    halted = []
    for name, tape0, q, extent, cap in cases:
        tape = dict(tape0)
        cells, left, right = initialize(tape, q, extent)
        p = 0
        active_count = 0
        min_x, max_x = left, right
        for T in range(cap + 1):
            expected = {x: tape.get(x, 0) for x in range(left - T + 1, right + T)}
            expected[left - T], expected[right + T] = FL, FR
            expected[p] = head(q, tape.get(p, 0))
            require(cells == expected, (name, T, 'TM/CA disagreement'))
            active_count += len(cells)
            min_x, max_x = min(min_x, min(cells)), max(max_x, max(cells))
            transition = DELTA[q + str(tape.get(p, 0))]
            if transition is None:
                bounds = shutdown_bounds(left, right, T, p)
                dl, dr = bounds['left_halt_distance'], bounds['right_halt_distance']
                for s in range(1, max(dl, dr) + 1):
                    cells = engine.step(cells)
                    total_updates += 1
                    expected_left = set(range(left - T - s, p - 2 * s)) if s < dl else set()
                    expected_right = set(range(p + 2 * s + 1, right + T + s + 1)) if s < dr else set()
                    require(set(cells) == expected_left | expected_right, (name, T, s, 'shutdown support'))
                    require(all((v in (0, 1, FL, FR) for v in cells.values())), 'test_lazy_u15.py: invariant at original line 91')
                    if expected_left:
                        require(cells[min(expected_left)] == FL, 'test_lazy_u15.py: invariant at original line 93')
                        require(all((cells[x] in (0, 1) for x in expected_left - {min(expected_left)})), 'test_lazy_u15.py: invariant at original line 94')
                    if expected_right:
                        require(cells[max(expected_right)] == FR, 'test_lazy_u15.py: invariant at original line 96')
                        require(all((cells[x] in (0, 1) for x in expected_right - {max(expected_right)})), 'test_lazy_u15.py: invariant at original line 97')
                    if cells:
                        min_x, max_x = min(min_x, min(cells)), max(max_x, max(cells))
                    active_count += len(cells)
                require(not cells, 'test_lazy_u15.py: invariant at original line 101')
                require(engine.step(cells) == {}, 'test_lazy_u15.py: invariant at original line 102')
                require(active_count == bounds['active_spacetime_cells'], (name, 'active count'))
                require((min_x, max_x) == (bounds['min_active_x'], bounds['max_active_x']), 'test_lazy_u15.py: invariant at original line 104')
                n = extent[1] - extent[0] + 1
                M = max(3, n)
                require(bounds['first_all_lazy_time'] <= M + 3 * T, 'test_lazy_u15.py: invariant at original line 107')
                halted.append({'case': name, 'T': T, 'p': p, **bounds})
                break
            if T == cap:
                break
            q, p = tm_step(tape, q, p)
            cells = engine.step(cells)
            total_updates += 1
    require(any((h['case'] == 'A_halt_T75_p_minus13' and h['T'] == 75 and (h['p'] == -13) for h in halted)), 'test_lazy_u15.py: invariant at original line 115')
    result = {
        'status': 'PASS',
        'literal_rule_count': sum(engine.counts.values()),
        'duplicate_patterns': 0,
        'cases': len(cases),
        'literal_CA_updates_checked': total_updates,
        'halting_cases_checked': len(halted),
        'halting_cases': halted,
        'checked': ['pure U15 table equality', 'deterministic complete rule hash',
                    'every step against independent TM state/tape oracle before halting',
                    'no malfunction on all tested evolutions',
                    'exact shutdown support at every post-halt row',
                    'exact extinction times and coordinate extrema',
                    'exact active spacetime counts', 'all-lazy fixed point',
                    'nearest-head-first pair parsing and initialization'],
    }
    (HERE / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'halting_cases'}, indent=2))


if __name__ == '__main__':
    main()
