#!/usr/bin/env python3
"""Independently check a radius-two invariant and a guarded TM shortcut.

Standard library only. This checker does not construct the invariant by
simulation. It checks its initial membership and all abstract transition
closures, admitting both values for every newly exposed exterior cell.
Then it checks the exact table edit and entire finite bootstrap endpoints.
The proof of why these finite checks imply halting equivalence is in PROOF.md.
This is an executable certificate checker, not a proof-assistant kernel.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
SOURCE_SHA = '84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95'
SHORTCUT_SHA = '78dcbd5aa7709f349cb9c378f54909e316c27d448537cf2e9dce15811152c2a4'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse(data):
    rows, start = {}, None
    for number, line in enumerate(data.decode('ascii').splitlines(), 1):
        if not line.strip():
            continue
        if line.startswith('#!'):
            m = re.fullmatch(r'#! start ([0-9]+)', line)
            require(m is not None and start is None, f'bad start at {number}')
            start = int(m[1])
            continue
        if line.startswith('#'):
            continue
        m = re.fullmatch(r'([0-9]+) ([01]) ([01]) ([LR]) ([0-9]+)', line)
        require(m is not None, f'bad row at {number}')
        q, b, w, d, target = m.groups()
        key = (int(q), int(b))
        require(key not in rows, f'duplicate row at {number}')
        rows[key] = (int(w), 1 if d == 'R' else -1, int(target))
    require(start == 0, 'the initial state must be 0')
    require(set(rows) == {(q, b) for q in range(253) for b in (0, 1)},
            'exactly 253 total binary working states are required')
    require(all(0 <= t <= 253 for _, _, t in rows.values()), 'invalid target')
    require(any(t == 253 for _, _, t in rows.values()), 'unreferenced terminal')
    return rows


def reachable_graph(rows):
    seen, todo = {0}, [0]
    while todo:
        q = todo.pop()
        if q == 253:
            continue
        for b in (0, 1):
            target = rows[q, b][2]
            if target not in seen:
                seen.add(target)
                todo.append(target)
    return seen


def check_invariant(rows, masks):
    require(len(masks) == 254, 'one bit mask is required for each control')
    require(all(type(m) is int and 0 <= m < (1 << 32) for m in masks),
            'each invariant mask must have exactly 32 possible pattern bits')
    require(masks[0] & 1, 'the all-zero initial window must be included')
    cases = 0
    for q in range(253):
        for p in range(32):
            if not (masks[q] >> p) & 1:
                continue
            b = (p >> 2) & 1
            w, d, target = rows[q, b]
            written = (p & ~(1 << 2)) | (w << 2)
            if d == 1:
                shifted, exterior = written >> 1, 1 << 4
            else:
                shifted, exterior = (written << 1) & 31, 1
            for p2 in (shifted, shifted | exterior):
                require((masks[target] >> p2) & 1,
                        f'closure fails at state {q}, window {p}, successor {p2}')
                cases += 1
    guarded_patterns = [p for p in range(32)
                        if (masks[60] >> p) & 1 and not (p >> 2) & 1]
    require(guarded_patterns == [8, 9, 24, 25], 'unexpected guarded patterns')
    require(all(not (p >> 1) & 1 for p in guarded_patterns),
            'state60/read0 does not force a zero in the left neighboring cell')
    return cases, guarded_patterns


def local_run(rows, state, head, ones, steps):
    ones = set(ones)
    for _ in range(steps):
        require(state != 253, 'unexpected local halt')
        w, d, target = rows[state, int(head in ones)]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += d
        state = target
    return state, head, ones


def check_macro(original, shortcut):
    changed = [key for key in original if original[key] != shortcut[key]]
    require(changed == [(60, 0)], 'the edit must change exactly state60/read0')
    require(original[60, 0] == (0, -1, 45), 'wrong original first row')
    require(original[45, 0] == (0, 1, 43), 'wrong original second row')
    require(original[43, 0] == (0, 1, 51), 'wrong original third row')
    require(shortcut[60, 0] == (0, 1, 51), 'wrong replacement row')
    count = 0
    # Arbitrary left-exterior/right cells within radius 2; the two touched
    # cells -1 and 0 must be zero. No macro step reads any other cell.
    for p in range(32):
        if ((p >> 1) & 1) or ((p >> 2) & 1):
            continue
        ones = {i - 2 for i in range(5) if (p >> i) & 1}
        before = local_run(original, 60, 0, ones, 3)
        after = local_run(shortcut, 60, 0, ones, 1)
        require(before == after == (51, 1, ones), 'whole-window macro mismatch')
        count += 1
    return count


def blank_run(rows, steps):
    q, head, ones, uses = 0, 0, set(), 0
    for _ in range(steps):
        require(q != 253, 'unexpected halt in bootstrap')
        b = int(head in ones)
        uses += int((q, b) == (60, 0))
        w, d, q = rows[q, b]
        if w:
            ones.add(head)
        else:
            ones.discard(head)
        head += d
    return {'state': q, 'head': head, 'one_cells': sorted(ones)}, uses


def expected_boot_shape():
    # Literal shape in upstream Boot253.boot_at_prefix330; state labels here
    # are compact. All unlisted cells of the bi-infinite tape are zero.
    values = [0, 2, 0, 0, 0, 0, 5, 0, 0]
    spare = [0, 0, 1, 0, 0, 0, 0, 0, 1] + [0] * 149
    ones = {-18, 23}
    position = 24
    for value in values + spare:
        position += 1  # block separator 0
        for _ in range(value + 1):
            ones.add(position)
            position += 1
    return {'state': 33, 'head': -17, 'one_cells': sorted(ones)}


def canonical_digest(value):
    data = json.dumps(value, sort_keys=True, separators=(',', ':')).encode('ascii')
    return hashlib.sha256(data).hexdigest()


def main():
    raw_original = (HERE / 'source_zfc253.tm').read_bytes()
    raw_shortcut = (HERE / 'zfc253_shortcut.tm').read_bytes()
    require(hashlib.sha256(raw_original).hexdigest() == SOURCE_SHA, 'source hash mismatch')
    require(hashlib.sha256(raw_shortcut).hexdigest() == SHORTCUT_SHA, 'shortcut hash mismatch')
    original, shortcut = parse(raw_original), parse(raw_shortcut)
    require(reachable_graph(original) == set(range(254)), 'source graph reachability mismatch')
    require(reachable_graph(shortcut) == set(range(254)), 'shortcut graph reachability mismatch')
    cert = json.loads((HERE / 'invariant_radius2.json').read_text())
    require(cert['radius'] == 2 and cert['source_sha256'] == SOURCE_SHA, 'wrong certificate input')
    masks = cert['state_pattern_masks']
    invariant_cases, guarded_patterns = check_invariant(original, masks)
    require(sum(m.bit_count() for m in masks) == 3530, 'unexpected invariant size')
    macro_cases = check_macro(original, shortcut)
    boot = json.loads((HERE / 'bootstrap_endpoint.json').read_text())
    expected = expected_boot_shape()
    require(boot['configuration'] == expected, 'boot data differs from exact upstream shape')
    digest = canonical_digest(expected)
    require(boot['configuration_sha256'] == digest, 'bootstrap digest mismatch')
    old_end, old_uses = blank_run(original, 312975)
    new_end, new_uses = blank_run(shortcut, 312895)
    require(old_end == new_end == expected, 'complete bootstrap endpoint mismatch')
    require(old_uses == new_uses == 40, 'wrong shortcut-use count')
    require(len(expected['one_cells']) == 178, 'wrong number of one-cells')
    result = {'status': 'all certificate checks passed',
              'working_states_original': 253, 'working_states_shortcut': 253,
              'separate_terminal': 253, 'source_sha256': SOURCE_SHA,
              'shortcut_sha256': SHORTCUT_SHA, 'radius': 2,
              'invariant_configurations': 3530, 'abstract_closure_cases': invariant_cases,
              'guarded_patterns': guarded_patterns, 'macro_cases': macro_cases,
              'source_boot_steps': 312975, 'shortcut_boot_steps': 312895,
              'bootstrap_shortcut_uses': 40, 'bootstrap_ones': 178,
              'bootstrap_configuration_sha256': digest,
              'proof_assistant_kernel_checked': False}
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
