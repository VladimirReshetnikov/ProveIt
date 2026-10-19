#!/usr/bin/env python3
"""Portable universal audit of a colored-context runtime.

The affine executor adds one free-word identity to the pinned executor:
b^(a*n) b = b^(a*n+1). All literal execution and box rules are unchanged.
The new rule merely joins a known singleton to an adjacent run of the same
symbol. It is useful when the run alone may be empty. Its soundness is the
definition of finite-word exponentiation and holds for every n>=0.

This script verifies runtime frames, not blank initialization or the
independent source-equivalence theorem.
"""
from pathlib import Path
from hashlib import sha256
import argparse
import json
import check_short_scanner as c


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--table', type=Path, required=True)
    ap.add_argument('--graph', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--scanner-zeros', type=int, choices=(8, 9), default=9)
    ap.add_argument('--baseline', type=Path,
                    default=Path(__file__).resolve().parent.parent/'sources/context246/zfc-context246')
    args = ap.parse_args()
    assert __debug__
    table = c.read_table(args.table)
    sites = c.graph_sites(args.graph)
    if args.scanner_zeros == 8:
        scanner = c.scanner_induction(table)
    else:
        chain = c.CHAIN + (74,)
        for i, q in enumerate(chain):
            target = chain[i+1] if i+1 < len(chain) else 84
            assert table[str(q), 0] == (0, 'L', str(target))
            assert table[str(q), 1] == (1, 'L', '4')
        assert table['84', 0] == (0, 'R', '84')
        assert table['84', 1] == (1, 'R', '96')
        scanner = dict(status='PASS unchanged nine-zero scanner',
                       distinguished_zero_run=9)
    affine_path = Path(__file__).resolve().with_name('colored_affine.py')
    affine = c.load_module(affine_path, 'colored_runtime_affine')
    review = c.load_module(args.baseline/'code/review_affine_source.py',
                           'colored_runtime_source_review')
    register_proofs = c.register_inductions(args.baseline, table)
    frames = c.check_instruction_frames(affine, review, table, sites)
    stats = dict(instruction_leaves=len(sites),
                 maximum_depth=max(len(p) for p, op, r in sites),
                 maximum_zero_run=max(max(map(len, p.split('1'))) for p, op, r in sites))
    result = dict(status=frames['status'],
                  table_sha256=sha256(args.table.read_bytes()).hexdigest(),
                  graph_sha256=sha256(args.graph.read_bytes()).hexdigest(),
                  affine_checker_sha256=sha256(affine_path.read_bytes()).hexdigest(),
                  working_states=len(table)//2, source_stats=stats,
                  scanner_induction=scanner, register_inductions=register_proofs,
                  instruction_frames=frames,
                  added_word_rule='b^(a*n) followed by b = b^(a*n+1), for a>0,n>=0',
                  added_word_rule_changes_no_state_head_or_tape=True,
                  blank_initialization_proved=False)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(dict(status=result['status'], working_states=len(table)//2,
                          register_inductions=register_proofs['status'],
                          source_stats=stats,
                          universally_verified_cases=frames['universally_verified_cases'],
                          failed_cases=len(frames['failures']),
                          added_rule_uses=frames['rule_counts'].get('join_right_singleton', 0)),
                     indent=2))


if __name__ == '__main__':
    main()
