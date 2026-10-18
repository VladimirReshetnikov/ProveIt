#!/usr/bin/env python3
"""Mixed-state folds of register routines, allowing any valid spare suffix.

Finite diagnostic only. All steps in the box samples are literal. A passed
sample is not promoted to an unbounded contract.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import sys
import time

BASE = Path('/workspace/scratch/bf00ce1dffdf/source/ProveIt/Computability/BusyBeaver/Research/ZFC')
sys.path.insert(0, str(BASE))
import candidate252_independent_audit as baseline
import permutation252_spare_fold_search as spare


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--fuel', type=int, default=2000)
    a = ap.parse_args()
    raw = (BASE/'candidate-permutation252/zfc_permutation252_old.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == baseline.EXPECTED_SHA
    table = baseline.read_table(raw)
    cases = list(spare.samples())
    usage = []
    for i, c in enumerate(cases):
        ok, reason, used, ticks = spare.run(table, c, a.fuel)
        assert ok, (i, reason)
        usage.append(used)
    states = sorted({q for q, _ in table})
    protected_targets = {table[k][2] for k in baseline.BOX_PAIRS}
    sources = sorted((baseline.BOX_STATES | protected_targets) - {64, 96})
    started = time.monotonic()
    result = dict(scope='Finite literal box samples, not an unbounded or blank-start proof.',
                  table_sha256=baseline.EXPECTED_SHA, fuel=a.fuel,
                  baseline_samples=len(cases), samples_checked=0,
                  recipes_checked=0, survivors=[], failures=[])
    reasons = Counter()
    for dead in sources:
        for target in states:
            if target == dead or target == 96:
                continue
            for copied_bit in (0, 1):
                if table[target, copied_bit] == table[dead, copied_bit]:
                    continue
                changed = {k: (w, d, target if t == dead else t)
                           for k, (w, d, t) in table.items() if k[0] != dead}
                w, d, t = table[dead, copied_bit]
                changed[target, copied_bit] = (w, d, target if t == dead else t)
                affected = {k for k, (_, _, t) in table.items()
                            if k[0] == dead or t == dead or k == (target, copied_bit)}
                order = sorted(range(len(cases)), key=lambda i: not bool(usage[i] & affected))
                failure = None
                for i in order:
                    ok, reason, used, ticks = spare.run(changed, cases[i], a.fuel, dead, target)
                    result['samples_checked'] += 1
                    if not ok:
                        failure = [dead, target, copied_bit, i, reason, ticks]
                        break
                result['recipes_checked'] += 1
                if failure is None:
                    result['survivors'].append([dead, target, copied_bit])
                else:
                    result['failures'].append(failure)
                    reasons[reason] += 1
        print('DONE', dead, result['recipes_checked'], len(result['survivors']), round(time.monotonic()-started, 2), flush=True)
    result['elapsed_seconds'] = time.monotonic()-started
    result['failure_reasons'] = dict(reasons)
    a.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('failures',)}))

if __name__ == '__main__':
    main()
