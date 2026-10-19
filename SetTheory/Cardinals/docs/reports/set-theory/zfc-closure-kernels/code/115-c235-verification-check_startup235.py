#!/usr/bin/env python3
"""Independent exact sparse/dense blank startup comparison.

This is a finite initialization proof. Universal runtime and logical
calibration require their separate certificates.
"""
import argparse
import hashlib
import json
from collections import Counter
from pathlib import Path

REFERENCE_SHA256 = 'ff059535876bc9e1e1e63174ebfd1c10a91c1a818ba0c3f8c4ef2ac51a3cfcc3'
TICKS = 409835


def require(condition, message):
    if not condition:
        raise ValueError(message)


def parse(path):
    data = path.read_bytes()
    table = {}
    start = None
    for line in data.decode().splitlines():
        if line.startswith('#! start '):
            require(start is None, 'Duplicate start header')
            start = int(line[9:])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require(b in (0, 1) and w in (0, 1) and d in ('L', 'R'), 'Malformed row')
            require((q, b) not in table, 'Duplicate row')
            table[q, b] = w, -1 if d == 'L' else 1, z
    states = {q for q, b in table}
    require(start in states and set(table) == {(q, b) for q in states for b in (0, 1)}, 'Incomplete table')
    require({z for w, d, z in table.values()} - states == {254}, 'Wrong halt')
    return table, start, hashlib.sha256(data).hexdigest()


def canonicalize(table, start):
    states = {q for q, b in table}
    order = [start] + sorted(states - {start})
    mapping = {q: i for i, q in enumerate(order)} | {254: len(states)}
    canonical = {(mapping[q], b): (w, d, mapping[z]) for (q, b), (w, d, z) in table.items()}
    data = ('#! start 0\n' + ''.join(f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
            for (q, b), (w, d, z) in sorted(canonical.items()))).encode()
    return canonical, mapping, data


def verify(reference_path, basis_path, candidate_path):
    reference, sr, hr = parse(reference_path)
    basis, sb, hb = parse(basis_path)
    candidate, sn, hn = parse(candidate_path)
    require(hr == REFERENCE_SHA256, 'Unexpected 236-state reference bytes')
    require(sr == sb == sn == 95, 'Unexpected initial states')
    require(len(reference) == len(basis) == 472 and len(candidate) == 470, 'Unexpected table censuses')
    canonical, mapping, canonical_data = canonicalize(candidate, sn)
    inverse = {value: key for key, value in mapping.items()}
    source_changes = {row for row in set(reference) | set(basis) if reference.get(row) != basis.get(row)}
    final_changes = {row for row in set(reference) | set(candidate) if reference.get(row) != candidate.get(row)}
    source_visits, final_visits, fold_visits = Counter(), Counter(), Counter()

    # Three separately represented executions: the pinned reference on an
    # unbounded sparse tape; the new basis on a dense inherited-label tape;
    # the candidate on an independently relabeled dense tape.
    offset = 8192
    dense_basis = bytearray(32768)
    dense_candidate = bytearray(32768)
    reference_ones = set()
    qr = qb = 95
    qc = 0
    pr = 0
    pb = pc = offset
    minimum_head = maximum_head = 0
    for tick in range(TICKS):
        require(qr == qb == inverse[qc] and pr == pb-offset == pc-offset,
                f'Checkpoint mismatch at {tick}')
        require(0 <= pb < len(dense_basis) and 0 <= pc < len(dense_candidate), 'Dense tape bound')
        br = int(pr in reference_ones)
        bb = dense_basis[pb]
        bc = dense_candidate[pc]
        require(br == bb == bc, f'Read mismatch at {tick}')
        row = qr, br
        if row in source_changes:
            source_visits[row] += 1
        if row in final_changes:
            final_visits[row] += 1
        if qr in (74, 193):
            fold_visits[qr] += 1
        wr, dr, zr = reference[qr, br]
        wb, db, zb = basis[qb, bb]
        wc, dc, zc = canonical[qc, bc]
        require((wr, dr, zr) == (wb, db, zb) == (wc, dc, inverse[zc]),
                f'Nonidentical initialization step at {tick}')
        if wr:
            reference_ones.add(pr)
        else:
            reference_ones.discard(pr)
        dense_basis[pb] = wb
        dense_candidate[pc] = wc
        qr, pr = zr, pr + dr
        qb, pb = zb, pb + db
        qc, pc = zc, pc + dc
        minimum_head = min(minimum_head, pr)
        maximum_head = max(maximum_head, pr)
    basis_ones = {i-offset for i, value in enumerate(dense_basis) if value}
    candidate_ones = {i-offset for i, value in enumerate(dense_candidate) if value}
    require(reference_ones == basis_ones == candidate_ones, 'Final whole-tape comparison failed')
    require(qr == qb == inverse[qc] == 96 and pr == pb-offset == pc-offset == -5, 'Wrong final state/head')
    require(len(reference_ones) == 351 and min(reference_ones) == -6, 'Wrong final tape inventory')
    require(not source_visits and not final_visits and not fold_visits, 'A changed row was visited')
    support = sorted(reference_ones)
    support_bytes = (json.dumps(support, separators=(',', ':')) + '\n').encode()
    return {'status': 'PASS_EXACT_BLANK_STARTUP_THREE_ENGINES',
            'reference_sha256': hr, 'basis_sha256': hb, 'candidate_sha256': hn,
            'canonical_candidate_sha256': hashlib.sha256(canonical_data).hexdigest(),
            'literal_steps_each': TICKS, 'synchronized_checkpoints': TICKS + 1,
            'initial_state_inherited': 95, 'initial_state_canonical': 0,
            'initial_head': 0, 'initial_tape': 'identically zero',
            'final_state_inherited': 96, 'final_state_canonical': mapping[96],
            'final_head': -5, 'marker_position': -6,
            'header_position': min(i for i in support if i >= -5),
            'head_range': [minimum_head, maximum_head],
            'one_cells': 351, 'final_support': support,
            'final_support_sha256': hashlib.sha256(support_bytes).hexdigest(),
            'all_other_cells_zero': True, 'full_tape_comparison': True,
            'basis_changed_rows': sorted(source_changes),
            'final_changed_rows_including_deleted': sorted(final_changes),
            'changed_row_visits': {}, 'special_state_visits': {},
            'dense_tape_bounds': [-offset, len(dense_candidate)-offset-1],
            'scope': 'The complete finite prescribed initialization. No infinite-runtime conclusion follows from this check alone.'}, canonical_data, mapping


def main():
    here = Path(__file__).resolve().parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reference', type=Path, required=True)
    parser.add_argument('--basis', type=Path, default=here/'basis236_seven_rotations74.tm')
    parser.add_argument('--candidate', type=Path, default=here/'candidate235_seven_rotations74.tm')
    parser.add_argument('--output', type=Path, default=here/'startup235.json')
    parser.add_argument('--canonical-output', type=Path)
    parser.add_argument('--renumbering-output', type=Path)
    args = parser.parse_args()
    result, canonical_data, mapping = verify(args.reference, args.basis, args.candidate)
    result['checker_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    if args.canonical_output:
        args.canonical_output.write_bytes(canonical_data)
    if args.renumbering_output:
        args.renumbering_output.write_text(json.dumps({'old_to_new': mapping, 'start_old': 95,
            'start_new': 0, 'halt_old': 254, 'halt_new': 235, 'dispatcher_old': 96,
            'dispatcher_new': mapping[96]}, indent=2) + '\n')
    print(json.dumps({key: value for key, value in result.items()
                     if key not in ('final_support', 'basis_changed_rows', 'final_changed_rows_including_deleted')}, indent=2))


if __name__ == '__main__':
    main()
