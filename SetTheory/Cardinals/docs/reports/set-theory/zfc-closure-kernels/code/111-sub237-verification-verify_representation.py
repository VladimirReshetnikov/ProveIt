#!/usr/bin/env python3
"""Inductive-window proof of an exact control/tape representation change.

This independently written checker reasons about arbitrary whole binary tapes.
It computes a finite inductive overapproximation of old reachable windows from
state 95, starting with EVERY window there. It then checks positive old/new
blocks for every admitted window, never reading outside the known window.

An accepted result is an ordinary finite-certificate halting-equivalence proof,
not a proof-assistant kernel theorem. Limits bound search for local blocks only.
All normal states map identically. One deleted state maps to a retained state,
optionally moving the head or toggling one tape cell relative to the OLD head.
Alternatively an adjacent tape bit selects between two retained controls; the
second retained state is excluded from OLD checkpoints and its incoming edges
are checked to be internal to blocks entered through the deleted state.
"""
from collections import deque, Counter
from pathlib import Path
import argparse
import hashlib
import json
import time


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read_table(path):
    table, start = {}, None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line.split()[-1])
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in table
        table[q, b] = w, 1 if d == 'R' else -1, z
    states = {q for q, _ in table}
    assert set(table) == {(q, b) for q in states for b in (0, 1)}
    assert {z for _, _, z in table.values()} - states == {254}
    # Older inherited-label tables have no header. The theorem checked by
    # this program explicitly starts at 95; a conflicting header is rejected.
    assert start in (None, 95)
    return table, states


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('old', type=Path)
    ap.add_argument('new', type=Path)
    ap.add_argument('--deleted', type=int, required=True)
    ap.add_argument('--retained', type=int, required=True)
    ap.add_argument('--shift', type=int, default=0)
    ap.add_argument('--flip-offset', type=int)
    ap.add_argument('--alternate-retained', type=int)
    ap.add_argument('--selector-offset', type=int)
    ap.add_argument('--selector-bit', type=int, choices=(0, 1), default=1)
    ap.add_argument('--radius', type=int, default=5)
    ap.add_argument('--old-cap', type=int, default=65)
    ap.add_argument('--new-cap', type=int, default=65)
    ap.add_argument('--output', type=Path, required=True)
    a = ap.parse_args()
    assert __debug__, 'Assertions must remain enabled'
    old, old_states = read_table(a.old)
    new, new_states = read_table(a.new)
    assert old_states - new_states == {a.deleted}
    assert new_states <= old_states and a.retained in new_states
    assert a.deleted not in (95, 254) and a.retained != 254
    assert a.radius >= 1 and 1 <= a.old_cap and 1 <= a.new_cap
    R, W = a.radius, 2*a.radius+1
    assert abs(a.shift) <= R
    assert a.flip_offset is None or abs(a.flip_offset) <= R
    excluded_checkpoints = set()
    if a.alternate_retained is not None:
        assert a.alternate_retained in new_states
        assert a.alternate_retained not in (95, a.retained)
        assert a.selector_offset is not None and abs(a.selector_offset) <= R
        # The old alternate state is an interior helper. Every external entry
        # to it is owned by a block beginning at the deleted state.
        assert all(q in (a.deleted, a.alternate_retained)
                   for (q, b), (_, _, z) in old.items()
                   if z == a.alternate_retained)
        excluded_checkpoints.add(a.alternate_retained)
    else:
        assert a.selector_offset is None
    size, mask, center = 1 << W, (1 << W)-1, 1 << R
    started = time.monotonic()

    # A finite abstract transition supplies both possible newly exposed bits.
    # This overapproximates every concrete tape, not a sample of executions.
    domains = {q: set() for q in old_states | {254}}
    domains[95] = set(range(size))
    queue = deque((95, tape) for tape in range(size))
    while queue:
        q, tape = queue.popleft()
        if q == 254:
            continue
        w, d, z = old[q, (tape >> R) & 1]
        written = (tape & ~center) | (w << R)
        if d == 1:
            lo = written >> 1
            successors = lo, lo | (1 << (W-1))
        else:
            lo = (written << 1) & mask
            successors = lo, lo | 1
        for successor in successors:
            if successor not in domains[z]:
                domains[z].add(successor)
                queue.append((z, successor))

    def mapped(q, h, tape):
        if q in excluded_checkpoints:
            return None
        if q == a.deleted:
            target = a.retained
            if a.alternate_retained is not None:
                selector_pos = h + a.selector_offset
                if not -R <= selector_pos <= R:
                    return None
                if ((tape >> (R+selector_pos)) & 1) != a.selector_bit:
                    target = a.alternate_retained
            if a.flip_offset is not None:
                pos = h + a.flip_offset
                if not -R <= pos <= R:
                    return None
                tape ^= 1 << (R + pos)
            return target, h+a.shift, tape
        return q, h, tape

    def step(table, config):
        q, h, tape = config
        if q == 254 or not -R <= h <= R:
            return None
        w, d, z = table[q, (tape >> (R+h)) & 1]
        tape = (tape & ~(1 << (R+h))) | (w << (R+h))
        return z, h+d, tape

    histogram, counts, failed = Counter(), Counter(), None
    checkpoint_states = old_states - excluded_checkpoints
    for q in sorted(checkpoint_states):
        for tape in sorted(domains[q]):
            old_start = q, 0, tape
            new_start = mapped(*old_start)
            assert new_start is not None
            old_first = step(old, old_start)
            new_first = step(new, new_start)
            assert old_first is not None
            target_first = mapped(*old_first)
            if new_first is not None and target_first == new_first:
                histogram[1, 1] += 1
                counts[q] += 1
                continue
            goals = {}
            config = old_start
            for k in range(1, a.old_cap+1):
                config = step(old, config)
                if config is None:
                    break
                goal = mapped(*config)
                if goal is not None:
                    goals.setdefault(goal, k)
            config, matched = new_start, None
            for k in range(1, a.new_cap+1):
                config = step(new, config)
                if config is None:
                    break
                if config in goals:
                    matched = goals[config], k
                    break
            if matched is None:
                failed = {'old_state': q, 'old_head': 0,
                          'window_integer': tape,
                          'window_bits_left_to_right': ''.join(str((tape>>i)&1) for i in range(W)),
                          'new_start': list(new_start)}
                break
            histogram[matched] += 1
            counts[q] += 1
        if failed:
            break
    domain_data = [[q, sorted(domains[q])] for q in sorted(domains)]
    domain_hash = hashlib.sha256(json.dumps(domain_data, separators=(',', ':')).encode()).hexdigest()
    result = {
        'status': 'NOT_PROVED' if failed else 'PASS_ALL_TAPE_POSITIVE_BLOCK_REPRESENTATION',
        'old_table_sha256': digest(a.old), 'new_table_sha256': digest(a.new),
        'checker_sha256': digest(Path(__file__)),
        'old_working_states': len(old_states), 'new_working_states': len(new_states),
        'start': 95, 'halt': 254,
        'representation': {'deleted': a.deleted, 'retained': a.retained,
                           'head_shift': a.shift, 'toggled_cell_offset': a.flip_offset,
                           'alternate_retained': a.alternate_retained,
                           'selector_offset': a.selector_offset,
                           'selector_bit_for_retained': a.selector_bit,
                           'excluded_old_checkpoint_states': sorted(excluded_checkpoints)},
        'radius': R, 'old_block_cap': a.old_cap, 'new_block_cap': a.new_cap,
        'inductive_domain_cases': sum(len(domains[q]) for q in old_states),
        'inductive_checkpoint_domain_cases': sum(len(domains[q]) for q in checkpoint_states),
        'inductive_domain_sha256': domain_hash,
        'verified_cases': sum(counts.values()),
        'state_case_counts': dict(sorted(counts.items())),
        'block_histogram': [{'old_steps': k[0], 'new_steps': k[1], 'cases': n}
                            for k, n in sorted(histogram.items())],
        'counterexample_to_this_local_certificate': failed,
        'seconds': time.monotonic()-started,
        'scope': 'All binary initial tapes and head positions from state95. Positive finite blocks. Every exterior cell remains arbitrary and is never read in an accepted block. Ordinary mathematical checker, not a kernel theorem.'
    }
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('state_case_counts',)}, indent=2))
    raise SystemExit(1 if failed else 0)


if __name__ == '__main__':
    main()
