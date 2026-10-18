#!/usr/bin/env python3
"""Replay exactly the rejected recipes whose first failure used an excluded guard.

The six guard exclusions are an input from the separately proved source phase
invariant. This script does not prove that invariant. Every survivor would
have to pass all other 8,385 instruction contracts. Failure is a sufficient
checker outcome, not a semantic counterexample.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import time
import synthesized_fusion as search

HERE = Path(__file__).resolve().parent
SIX = {8202, 8203, 8204, 8358, 8359, 8360}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--ledger', type=Path, default=HERE/'evidence/fusion-clean.jsonl')
    parser.add_argument('--output', type=Path, default=HERE/'evidence/phase-followup-recheck.json')
    args = parser.parse_args()
    assert __debug__
    assert hashlib.sha256(args.ledger.read_bytes()).hexdigest() == '60e7a44066339e0979cb4ad172c0f0368812fe305fbfa1b928262da40946d690'
    rows = [row for line in args.ledger.read_text().splitlines() if (row := json.loads(line))[6] in SIX]
    assert len(rows) == 1674
    strict, table, _, cases, _, _ = search.setup()
    protected = {(str(q), b) for q, b in search.audit.BOX_PAIRS}
    result = {'scope': __doc__, 'planned': len(rows), 'checked': 0, 'case_checks': 0,
              'excluded_source_cases': sorted(SIX), 'survivors': [], 'results': [], 'reasons': Counter()}
    began = time.monotonic()
    witnesses = [8390, 8236, 8271]
    for row in rows:
        dead, keep, bit, write, direction, target, previous_failure, _ = row
        dead, keep, target = str(dead), str(keep), str(target)
        candidate = {k: (w, d, keep if t == dead else t) for k, (w, d, t) in table.items() if k[0] != dead}
        candidate[keep, bit] = write, direction, target
        assert len(candidate) == 502
        assert all(candidate[k] == table[k] for k in protected)
        failed = None
        message = None
        # Witnesses only select early rejection. The complete retained list
        # follows, and must be exhausted for a recipe to count as a survivor.
        order = witnesses + [i for i in range(len(cases)) if i not in SIX and i not in witnesses]
        for i in order:
            pc, op, guard, goal = cases[i]
            result['case_checks'] += 1
            try:
                _, literal = strict.run(candidate, pc, guard, goal, halt=(op == 'CH'), fuel=1000)
                assert literal > 0
            except (AssertionError, KeyError) as error:
                failed, message = i, str(error)
                break
        result['checked'] += 1
        if failed is None:
            result['survivors'].append(row[:6])
        else:
            assert failed not in SIX
            result['reasons'][str(failed)] += 1
            if failed not in witnesses:
                witnesses.insert(0, failed)
        result['results'].append({'recipe': row[:6], 'previous_failure': previous_failure,
                                  'failure': failed, 'message': message})
    result['status'] = 'completed'
    result['elapsed_seconds'] = time.monotonic()-began
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print({k: v for k, v in result.items() if k not in {'results', 'scope'}})


if __name__ == '__main__':
    main()
