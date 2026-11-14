#!/usr/bin/env python3
"""Source-conditioned windows with spare=1 and inductive counter intervals.

Uses the fixed-spare specialization developed in logic_audit/restricted_runtime.py
and its independently checked interval data. Every included primitive contract
is still proved over arbitrary permitted natural primary values, arbitrary gap,
and an arbitrary nonempty finite spare list of ones. Unary loop interiors are
expanded only as far as the requested bounded tape window. Discovery data alone
is not a machine correctness certificate; every proposed reduction must replay
the specialized whole-tape contracts and the literal startup.
"""
import argparse
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import sys
import time
import source_context_harvest as h

ROOT = h.ROOT
PACKET = h.PACKET


def bounded(atoms, n):
    return tuple(a + (1,) if a[0] == 'list' else a
                 for a in h.bounded_atoms(atoms, n))


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--radius', type=int, default=4)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    radius = a.radius
    sys.path.insert(0, str(PACKET / 'code'))
    import check_runtime as replay
    s = replay.s
    table_path = PACKET / 'machine/u208.native.tm'
    table = replay.read(table_path)
    sites = json.loads((PACKET / 'machine/sites.json').read_text())
    facts_path = ROOT / 'logic_audit/source_intervals.json'
    facts_data = json.loads(facts_path.read_text())
    facts = facts_data['conditional_intervals']
    cap = facts_data['cap']
    windows = {q: set() for q, b in table}
    original_step = s.State.step
    original_var = s.var
    started = time.monotonic()
    calls = 0

    @lru_cache(None)
    def nearby(left, right, direction):
        nl = radius if direction == 1 else radius + 1
        nr = radius + 1 if direction == 1 else radius
        return frozenset(int(x[::-1] + y, 2)
                         for x in h.prefix_words(left, nl)
                         for y in h.prefix_words(right, nr))

    @lru_cache(None)
    def scan_windows(dst, rest, direction, bit, write, lower, variable):
        result = set()
        for consumed in range(radius + 1):
            for remaining in range(1, radius + 2):
                if variable:
                    possible = (consumed == radius or remaining == radius + 1
                                or consumed + remaining >= lower)
                elif consumed == radius and remaining == radius + 1:
                    possible = lower >= consumed + remaining
                elif consumed == radius:
                    possible = lower - remaining >= consumed
                elif remaining == radius + 1:
                    possible = lower - consumed >= remaining
                else:
                    possible = consumed + remaining == lower
                if not possible:
                    continue
                back = (('run', write, consumed, False),) + dst
                front = (('run', bit, remaining, False),) + rest
                left, right = (back, front) if direction == 1 else (front, back)
                result.update(nearby(left, right, direction))
        return frozenset(result)

    def step(state, table, lemmas, clock, motion):
        nonlocal calls
        state.key()
        q, direction = state.q, state.direction
        nl = radius if direction == 1 else radius + 1
        nr = radius + 1 if direction == 1 else radius
        windows[q].update(nearby(bounded(state.left, nl), bounded(state.right, nr), direction))
        src, dst = (state.right, state.left) if direction == 1 else (state.left, state.right)
        if src and src[0][0] == 'run':
            atom = src[0]
            write, move, target = table[q, atom[1]]
            if target == q and move == direction:
                windows[q].update(scan_windows(bounded(dst, radius), bounded(src[1:], radius + 1),
                                               direction, atom[1], write,
                                               min(atom[2][0], 2 * radius + 2),
                                               any(atom[2][1:])))
        calls += 1
        return original_step(state, table, lemmas, clock, motion)

    s.State.step = step
    s.var = lambda i: s.num(1) if i == 2 else original_var(i)
    try:
        lemmas, blocks = s.prove_blocks(table)
    finally:
        s.var = original_var
    for block in blocks:
        block['steps'] = '3'
        block['block_value'] = 1
    cases = []
    used = set()
    total = 0
    for index, site in enumerate(sites):
        for positive in ((False, True) if site[1] == 'CD' else (False,)):
            constraints = facts[f'{index}:{int(positive)}']
            if constraints is None:
                continue
            def value(i):
                if i == 11:
                    return s.num(1)
                if 2 <= i <= 10:
                    reg = i - 2
                    lo, hi = constraints[reg]
                    if site[1] == 'CD' and reg == site[2]:
                        if not positive:
                            return original_var(i)
                        lo = max(1, lo) - 1
                        if hi < cap:
                            hi -= 1
                    if lo == hi and hi < cap:
                        return s.num(lo)
                    return s.add(s.num(lo), original_var(i))
                return original_var(i)
            s.var = value
            try:
                result = s.case(table, lemmas, site, positive)
            finally:
                s.var = original_var
            used.update(result['rows'])
            total += result['symbolic_steps']
            cases.append({'site_index': index, 'positive': positive,
                          'duration': result['duration'],
                          'symbolic_steps': result['symbolic_steps']})
        if (index + 1) % 500 == 0:
            print('CONTRACTS', index + 1, len(cases), round(time.monotonic() - started, 2), flush=True)
    for block in blocks:
        for event in block['trace']:
            used.add(tuple(event[1][:2]))
    if used != set(table):
        raise ValueError(('Uncovered literal rows', sorted(set(table) - used)))
    q = head = 0
    ones = set()
    for tick in range(48140):
        word = ''.join(str(int(head + d in ones)) for d in range(-radius, radius + 1))
        windows[q].add(int(word, 2))
        w, d, z = table[q, int(head in ones)]
        ones.add(head) if w else ones.discard(head)
        q, head = z, head + d
    result = {'scope': __doc__, 'radius': radius,
              'input_table': str(table_path.relative_to(ROOT)),
              'input_sha256': hashlib.sha256(table_path.read_bytes()).hexdigest(),
              'facts_path': str(facts_path.relative_to(ROOT)),
              'facts_sha256': hashlib.sha256(facts_path.read_bytes()).hexdigest(),
              'runtime': {'status': 'RESTRICTED_UNIVERSAL_RUNTIME_PASS',
                          'contracts': len(cases), 'symbolic_inferences': total,
                          'literal_rows_covered': len(used), 'blocks': blocks,
                          'spares': 'nonempty finite list of value1; symbolic tail width multiple3'},
              'hook_calls': calls, 'startup_steps': 48140,
              'startup_endpoint': [q, head], 'window_count': sum(map(len, windows.values())),
              'window_counts': {q: len(v) for q, v in windows.items()},
              'windows': {q: sorted(v) for q, v in windows.items()},
              'seconds': time.monotonic() - started,
              'cache_info': {'nearby': str(nearby.cache_info()),
                             'scan_windows': str(scan_windows.cache_info()),
                             'prefix_words': str(h.prefix_words.cache_info())}}
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    a.output.with_suffix('.cases.json').write_text(json.dumps(cases, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('windows', 'runtime', 'window_counts')}, indent=2))


if __name__ == '__main__':
    main()
