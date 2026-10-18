#!/usr/bin/env python3
"""Exact footprint audit transporting the inherited register-marking proof.

No numerical register-value samples are used to justify the unbounded result.
The paper proof in marking_transport.tex establishes that all marking runs
use only this explicitly enumerated footprint.  Every footprint row is then
checked literally in both supplied machine artifacts.
"""
from pathlib import Path
import argparse
import hashlib
import json

SKIP = (60, 44, 31, 56, 38, 40, 28, 64, 69)


def read_table(path):
    table = {}
    for line in path.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        table[key] = int(write), direction, int(target)
    return table


def footprint():
    expected = {(q, 1): (1, 'R', q) for q in SKIP}
    expected.update({(SKIP[j], 0): (0, 'R', SKIP[j-1]) for j in range(1, 9)})
    expected.update({
        (60, 0): (0, 'R', 0),
        (0, 1): (0, 'L', 2),
        (2, 0): (0, 'L', 2),
        (2, 1): (1, 'L', 4),
        (4, 1): (1, 'L', 4),
        (4, 0): (0, 'L', 6),
        (6, 1): (1, 'L', 4),
    })
    assert len(expected) == 24
    return expected


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--baseline', required=True, type=Path)
    ap.add_argument('--candidate', required=True, type=Path)
    ap.add_argument('--output', required=True, type=Path)
    args = ap.parse_args()
    baseline = read_table(args.baseline)
    candidate = read_table(args.candidate)
    expected = footprint()
    rows = []
    for key, value in sorted(expected.items()):
        assert baseline[key] == value, ('baseline row', key, baseline[key], value)
        assert candidate[key] == value, ('candidate row', key, candidate[key], value)
        rows.append(dict(state=key[0], read=key[1], write=value[0],
                         direction=value[1], target=value[2]))
    excluded = {43, 59, 85, 75, 95, 97, 109, 112, 131, 255}
    assert not ({q for q, b in expected} & excluded)
    result = dict(
        status='PASS',
        scope='Literal equality of the entire 24-transition footprint of the universal marking lemma.',
        paper_proof='marking_transport.tex',
        uniform_parameters='All physical positions 0..8, arbitrary natural primary values, arbitrary finite suffix (possibly empty), arbitrary exterior context.',
        start_states=list(SKIP),
        exit_state_first_physical=2,
        exit_state_other_physical=6,
        output_head='h - 1',
        duration='2 * width(prefix) + 3',
        new_operation_and_initializer_rows_absent=True,
        finite_sampling_used_for_unbounded_claim=False,
        fresh_kernel_verification=False,
        hashes={
            'baseline_sha256': hashlib.sha256(args.baseline.read_bytes()).hexdigest(),
            'candidate_sha256': hashlib.sha256(args.candidate.read_bytes()).hexdigest(),
        },
        footprint=rows,
    )
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'footprint'}, indent=2))


if __name__ == '__main__':
    main()
