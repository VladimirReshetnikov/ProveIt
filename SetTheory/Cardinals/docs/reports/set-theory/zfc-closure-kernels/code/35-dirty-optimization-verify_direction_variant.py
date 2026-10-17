#!/usr/bin/env python3
"""Standalone finite verifier for a certified 253-state direction rewrite.

Only Python's standard library is required. This script does not import any
search implementation. It parses both literal tables, checks their entire
one-row difference, recomputes the finite abstract invariant, and literally
replays both programs on every five-cell window admitted by the certificate.
The accompanying note supplies the induction from these checks to blank-tape
halting equivalence. This Python program is not a proof-assistant kernel.
"""
import argparse
from collections import defaultdict, deque
import hashlib
import json
from pathlib import Path
import re


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse(data):
    start, rows = None, {}
    for line in data.decode('utf-8').splitlines():
        line = line.strip()
        if line.startswith('#!'):
            m = re.fullmatch(r'#!\s+start\s+(\d+)', line)
            require(m is not None and start is None, 'invalid or duplicate start')
            start = int(m[1])
        elif line and not line.startswith('#'):
            m = re.fullmatch(r'(\d+)\s+([01])\s+([01])\s+([LR])\s+(\d+)', line)
            require(m is not None, 'malformed transition')
            q, read, write, move, target = m.groups()
            pair = int(q), int(read)
            require(pair not in rows, 'duplicate transition')
            rows[pair] = int(write), 1 if move == 'R' else -1, int(target)
    states = {q for q, _ in rows}
    require(set(rows) == {(q, b) for q in states for b in (0, 1)}, 'incomplete machine')
    require(start in states, 'missing start state')
    terminals = {e[2] for e in rows.values()} - states
    require(len(terminals) == 1, 'need exactly one referenced terminal')
    return start, next(iter(terminals)), states, rows


def reachable_windows(start, halt, rows, radius):
    width = 2 * radius + 1
    full = (1 << width) - 1
    seen, queue = {(start, 0)}, deque([(start, 0)])
    while queue:
        state, pattern = queue.popleft()
        if state == halt:
            continue
        write, movement, target = rows[state, (pattern >> radius) & 1]
        new = (pattern & ~(1 << radius)) | (write << radius)
        if movement == 1:
            new >>= 1
            exterior_bit = 1 << (width - 1)
        else:
            new = (new << 1) & full
            exterior_bit = 1
        for successor in (new, new | exterior_bit):
            item = target, successor
            if item not in seen:
                seen.add(item)
                queue.append(item)
    return seen


def satisfies(pattern, radius, guard):
    return all(((pattern >> (offset + radius)) & 1) == bit for offset, bit in guard)


def run(rows, halt, state, pattern, radius, steps):
    head = 0
    ones = {i - radius for i in range(2 * radius + 1) if pattern & (1 << i)}
    require(isinstance(steps, int) and steps > 0, 'strictly positive progress required')
    for _ in range(steps):
        require(state != halt, 'attempted step after halt')
        require(-radius <= head <= radius, 'attempted read outside known window')
        write, move, target = rows[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move
        state = target
    return state, head, frozenset(ones)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('baseline', type=Path)
    ap.add_argument('variant', type=Path)
    ap.add_argument('certificate', type=Path)
    ap.add_argument('--output', type=Path)
    args = ap.parse_args()
    base_raw, variant_raw = args.baseline.read_bytes(), args.variant.read_bytes()
    cert = json.loads(args.certificate.read_text())
    require(cert['schema'] == 'direction-rewrite-v1', 'unsupported certificate schema')
    require(hashlib.sha256(base_raw).hexdigest() == cert['baseline_sha256'], 'baseline hash mismatch')
    require(hashlib.sha256(variant_raw).hexdigest() == cert['variant_sha256'], 'variant hash mismatch')
    astart, ahalt, astates, arows = parse(base_raw)
    bstart, bhalt, bstates, brows = parse(variant_raw)
    require((astart, ahalt, astates) == (bstart, bhalt, bstates), 'state domain/start/halt differ')
    require(len(astates) == cert['working_states'] == 253, 'wrong state count')
    require((astart, ahalt) == (cert['start'], cert['halt']) == (0, 253), 'wrong start/halt')
    patch = tuple(cert['modified_pair'])
    require(patch == (131, 1), 'unexpected modified pair')
    differences = {r for r in arows if arows[r] != brows[r]}
    require(differences == {patch}, 'literal tables must differ at exactly the advertised row')
    require(arows[patch] == tuple(cert['old_transition']) == (0, -1, 20), 'old row mismatch')
    require(brows[patch] == tuple(cert['new_transition']) == (0, 1, 22), 'new row mismatch')

    radius = cert['window_radius']
    require(radius == 2, 'this compact certificate uses radius 2')
    cases = cert['cases']
    for case in cases:
        require(isinstance(case['guard'], list), 'malformed guard')
        for offset, bit in case['guard']:
            require(isinstance(offset, int) and -radius <= offset <= radius and bit in (0, 1), 'guard outside window')
    abstract = reachable_windows(astart, ahalt, arows, radius)
    needed = sorted(bits for q, bits in abstract if q == patch[0] and (bits >> radius) & 1 == patch[1])
    require(len(abstract) == cert['expected_abstract_configurations'], 'abstract census mismatch')
    require(len(needed) == cert['expected_modified_row_windows'], 'modified-row census mismatch')

    covered = set()
    case_counts = [0] * len(cases)
    for pattern in range(1 << (2 * radius + 1)):
        if (pattern >> radius) & 1 != patch[1]:
            continue
        matching = [i for i, case in enumerate(cases) if satisfies(pattern, radius, case['guard'])]
        require(len(matching) <= 1, 'overlapping certificate cases')
        if not matching:
            continue
        i = matching[0]
        case = cases[i]
        old = run(arows, ahalt, patch[0], pattern, radius, case['original_steps'])
        new = run(brows, bhalt, patch[0], pattern, radius, case['variant_steps'])
        require(old == new, f'failed whole-window match for pattern {pattern}')
        require(old[:2] == (case['common_state'], case['common_head']), 'unexpected common control/head')
        covered.add(pattern)
        case_counts[i] += 1
    require(set(needed) <= covered, 'guard fails for an abstractly reachable modified-row window')
    require(len(covered) == cert['expected_local_window_checks'], 'local case census mismatch')
    out = {'all_checks_passed': True, 'working_states': len(astates),
           'modified_pair': list(patch), 'abstract_configurations': len(abstract),
           'abstractly_possible_modified_row_windows': len(needed),
           'local_windows_replayed': len(covered), 'case_window_counts': case_counts,
           'equivalence': 'blank halting equivalent by the accompanying positive-progress whole-tape block argument',
           'state_count_improvement': False,
           'baseline_sha256': cert['baseline_sha256'], 'variant_sha256': cert['variant_sha256'],
           'certificate_sha256': hashlib.sha256(args.certificate.read_bytes()).hexdigest(),
           'verifier_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'verification_level': 'standalone finite executable verification with mathematical soundness argument; not kernel-checked'}
    encoded = json.dumps(out, indent=2) + '\n'
    if args.output:
        args.output.write_text(encoded)
    print(encoded, end='')


if __name__ == '__main__':
    main()
