#!/usr/bin/env python3
"""Independent finite certificate for the four-row predecessor-selector FM215.

The local check covers every tape under a two-clause invariant. The proof in
README.md explains why these finite facts imply unbounded halting equivalence.
No finite blank run is used as a substitute for that simulation theorem.
"""
from pathlib import Path
import argparse
import hashlib
import json
from collections import deque

HERE = Path(__file__).resolve().parent
PARENT_SHA = '9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
NEW_SHA = '3ece1233f11d33375425221c5bcedba941e073763912990eabf321197772dce5'
DENSE_SHA = '1b602d3b37887060ce2d992cf3036f540e8ccff5d37ab06c80f19f1edd38cbc6'
PATCH = {(124, 0): (0, -1, 127), (127, 0): (0, 1, 8),
         (127, 1): (1, 1, 109), (110, 0): (0, 1, 124)}


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def parse(path):
    table, start = {}, 0
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            start = int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q, b, w, d, n = line.split()
        key = int(q), int(b)
        assert key not in table and d in ('L', 'R')
        assert int(b) in (0, 1) and int(w) in (0, 1)
        table[key] = int(w), 1 if d == 'R' else -1, int(n)
    states = {q for q, _ in table}
    assert all((q, b) in table for q in states for b in (0, 1))
    return table, start


def phi(q):
    return 124 if q == 127 else q


def canonical(table, start=0, reflect=False):
    ids, queue, result = {start: 0}, [start], []
    for q in queue:
        if (q, 0) not in table:
            result.append(['halt'])
            continue
        rows = []
        for b in (0, 1):
            w, d, n = table[q, b]
            if n not in ids:
                ids[n] = len(ids)
                queue.append(n)
            rows.append([w, -d if reflect else d, ids[n]])
        result.append(rows)
    return json.dumps(result, separators=(',', ':')), len(queue)


def local_step(table, state, head, tape):
    assert head in tape, 'Unexpected read outside explicitly split local cells'
    w, d, n = table[state, tape[head]]
    tape[head] = w
    return n, head + d


def verify_local(parent, new):
    assert {k: v for k, v in new.items() if parent[k] != v} == PATCH
    assert {k: v for k, v in parent.items() if v[2] == 124} == {(104, 1): (1, 1, 124)}
    assert {k: v for k, v in parent.items() if v[2] == 127} == {(110, 0): (0, 1, 127)}
    assert parent[124, 1] == parent[127, 1] == (1, 1, 138)
    cases, clocks = 0, {1: 0, 3: 0}
    for q in sorted({q for q, _ in parent}):
        for code in range(8):
            tape = {-1: code & 1, 0: (code >> 1) & 1, 1: (code >> 2) & 1}
            if q == 124 and tape[-1] != 1:
                continue
            if q == 127 and tape[-1] != 0:
                continue
            old_tape, new_tape = tape.copy(), tape.copy()
            old_q, old_h = local_step(parent, q, 0, old_tape)
            n = 3 if q in (124, 127) and tape[0] == 0 else 1
            new_q, new_h = phi(q), 0
            for _ in range(n):
                assert (new_q, 0) in new
                new_q, new_h = local_step(new, new_q, new_h, new_tape)
            assert new_q == phi(old_q) and new_h == old_h
            assert new_tape == old_tape
            cases += 1
            clocks[n] += 1
    return {'local_split_cases': cases, 'duration_case_counts': clocks,
            'invariant': ['old state 124 implies predecessor bit 1',
                          'old state 127 implies predecessor bit 0'],
            'uninspected_cells': 'Never read or written; arbitrary exterior is framed out.'}


def sparse_step(table, q, h, ones):
    b = int(h in ones)
    w, d, n = table[q, b]
    if w:
        ones.add(h)
    else:
        ones.discard(h)
    return n, h + d


def verify_boot(parent, new):
    oq = nq = oh = nh = 0
    ot, nt = set(), set()
    new_steps = marked = 0
    for i in range(95714):
        n = 3 if oq in (124, 127) and oh not in ot else 1
        marked += int(n == 3)
        oq, oh = sparse_step(parent, oq, oh, ot)
        for _ in range(n):
            nq, nh = sparse_step(new, nq, nh, nt)
        new_steps += n
        assert (nq, nh, nt) == (phi(oq), oh, ot), ('boundary', i)
    assert (oq, nq, oh, nh, len(ot)) == (84, 84, -8, -8, 95)
    assert new_steps == 95840 and marked == 63
    return {'old_steps': 95714, 'new_steps': new_steps, 'three_step_visits': marked,
            'native_state': nq, 'head': nh, 'one_cells': sorted(nt),
            'zero_exterior': True, 'every_simulation_boundary_checked': True}


def compare_repository(root, target):
    records, signatures, matches, failures = [], set(), [], 0
    for path in sorted(root.rglob('*.tm')):
        try:
            table, start = parse(path)
        except (ValueError, AssertionError, UnicodeError, OSError):
            failures += 1
            continue
        if len(table) != 430:
            continue
        sig, count = canonical(table, start)
        if count != 216:
            continue
        signatures.add(sig)
        reflected, _ = canonical(table, start, reflect=True)
        record = {'path': str(path.relative_to(root)), 'sha256': sha(path)}
        records.append(record)
        if target in (sig, reflected):
            matches.append(record)
    assert not matches, matches
    return {'literal_tables': len(records), 'distinct_rooted_graphs': len(signatures),
            'matches_including_global_reflection': matches,
            'nonparseable_tm_files_skipped': failures, 'corpus': records,
            'scope': 'Finite repository comparison, not a global novelty claim.'}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--repo', type=Path)
    ap.add_argument('--output', type=Path, default=HERE / 'fm215_checks.json')
    args = ap.parse_args()
    parent_path, new_path, dense_path = HERE / 'tables/00.tm', HERE / 'fm215.native.tm', HERE / 'fm215.tm'
    assert (sha(parent_path), sha(new_path), sha(dense_path)) == (PARENT_SHA, NEW_SHA, DENSE_SHA)
    parent, ps = parse(parent_path)
    new, ns = parse(new_path)
    dense, ds = parse(dense_path)
    assert ps == ns == ds == 0 and len(parent) == len(new) == len(dense) == 430
    sig, count = canonical(new)
    assert count == 216 and canonical(dense)[0] == sig
    assert canonical(parent)[0] != sig and canonical(parent, reflect=True)[0] != sig
    result = {'status': 'FINITE_CERTIFICATE_PASS', 'working_states': 215, 'rows': 430,
              'separate_halt': 254, 'new_sha256': NEW_SHA, 'dense_sha256': DENSE_SHA,
              'parent_sha256': PARENT_SHA, 'changed_rows': 4,
              'local_certificate': verify_local(parent, new),
              'blank_prefix': verify_boot(parent, new),
              'source_change': False}
    if args.repo:
        result['novelty'] = compare_repository(args.repo, sig)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('blank_prefix', 'novelty')}, indent=2))
    print('Blank prefix:', result['blank_prefix']['new_steps'], 'steps')
    if args.repo:
        print('Corpus:', result['novelty']['literal_tables'], 'tables,',
              result['novelty']['distinct_rooted_graphs'], 'graphs; no match')


if __name__ == '__main__':
    main()
