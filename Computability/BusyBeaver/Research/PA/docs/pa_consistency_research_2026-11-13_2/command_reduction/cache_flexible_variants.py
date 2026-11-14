#!/usr/bin/env python3
"""Measure two cache-flexible MP source candidates; neither is a binary TM.

Both reuse the literal pinned source definitions.  Candidate one uses a
two-decrement equality-to-one test. Candidate two uses a positive consequent
d+x+1, so a zero raw cache marks contradiction.  The complete MP macros are
checked on bounded exact-integer inputs, with all nine registers compared.
"""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

from reconstruct_halt_at_mp import PROGRAM_SHA256, count_internal, parse_program, sites
from halt_at_mp_source_checks import frame, pair, resolve, run

HERE = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise RuntimeError('Run without Python -O or -OO; assertions are required.')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--program', type=Path,
                        default=HERE.parent / 'rotated196/upstream/PA196/Program.lean')
    parser.add_argument('--output', type=Path,
                        default=HERE / 'cache_flexible_variants')
    args = parser.parse_args()
    raw = args.program.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == PROGRAM_SHA256
    n = parse_program(raw)
    # After a positive test consumes one raw cache unit, node54 copies the
    # remainder into T while retaining D, then two increments restore T.
    body = ((n['node54'], n['node60']), ('CB', 1))
    positive_success = ((('CD', 4), body), ('CH', None))
    standard_success = (('CD', 4), positive_success)
    results = []
    args.output.mkdir(parents=True, exist_ok=True)
    for positive, success in [(False, standard_success), (True, positive_success)]:
        name = 'positive_consequent' if positive else 'two_decrement_test'
        # x11 is incT followed by the existing implication constructor.
        prelude = ((n['node74'], n['x11']), n['node37']) if positive else n['node162']
        mp = (prelude, (n['node6'], success))
        dispatch = (('CD', 3), ((n['node161'], mp), ('CC', 3)))
        shift = (n['node145'], (('CD', 5), n['node38']))
        root = (n['node20'], ((n['node36'], (dispatch, shift)), ('CC', 2)))
        rows = sites(root)
        graph = resolve(rows)
        mp_entry = next(i for i, (p, _, _) in enumerate(rows) if p.startswith('10101010'))
        cases = 0
        max_steps = 0
        for t, d, x, w, tail in itertools.product(range(4), range(4), range(4), range(3), range(3)):
            raw_cache = d + x
            b = raw_cache + int(positive)
            major = 4 * pair(t, b)
            for h in sorted({0, 1, major, major + 1}):
                initial = frame(t, w, d, h, pair(x, tail), marker=17)
                status, got, steps = run(graph, mp_entry, initial)
                ok = major == h
                assert status == ('halt' if ok and b == 1 else 'return')
                if ok:
                    expected_d = max(0, b - 2)
                else:
                    expected_d = raw_cache
                expected = frame(b if ok and b != 1 else 0, w, expected_d,
                                 0, tail, marker=17)
                assert got == expected, (name, initial, b, status, got, expected)
                max_steps = max(max_steps, steps)
                cases += 1
        data = (json.dumps(rows, separators=(',', ':')) + '\n').encode()
        (args.output / (name + '.sites.json')).write_bytes(data)
        results.append({
            'candidate': name,
            'source_sites': len(rows),
            'internal_dag_nodes': count_internal(root),
            'complete_mp_tests': cases,
            'maximum_source_steps': max_steps,
            'source_sha256': hashlib.sha256(data).hexdigest(),
            'status': 'bounded MP checks passed; more internal nodes than halt-at-MP baseline',
        })
    receipt = {'upstream_internal_dag_nodes': 159,
               'original_halt_at_mp_internal_dag_nodes': 162,
               'candidates': results,
               'scope': 'Source experiments only; no smaller physical TM established.'}
    (args.output / 'results.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
