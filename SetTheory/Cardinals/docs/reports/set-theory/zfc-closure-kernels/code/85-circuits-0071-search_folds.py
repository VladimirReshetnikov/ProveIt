#!/usr/bin/env python3
"""Search uniform and mixed decoder folds with all macro-support rows protected.

Default scope reproduces this archive's five new-layout searches: at least one
state of each pair has a changed decoder row relative to Context246. Optional
--domain product enables the new extra-known-zero-test oracle. A rejected
bounded symbolic run is not an impossibility proof. See README.md for details.
"""
from collections import Counter, defaultdict
import argparse
import json
from pathlib import Path
from common import OUTPUT
from affine_checker import AffineChecker, BASE_TABLE, PROTECTED, Tracking


def run(layout, domain, all_pairs, fuel, output):
    checker = AffineChecker(layout, domain)
    table = checker.table
    states = sorted({q for q, bit in table}, key=int)
    targets = {table[key][2] for key in PROTECTED}
    dead = [q for q in states if q != '96' and q not in targets
            and all((q, bit) not in PROTECTED for bit in (0, 1))]
    changed = {q for q in states if any(table[q, bit] != BASE_TABLE.get((q, bit)) for bit in (0, 1))}
    usage = defaultdict(set)
    cost = []
    for index in range(len(checker.cases)):
        tracking = Tracking(table)
        ok, count, error = checker.check(tracking, index, fuel)
        assert ok, ('baseline', layout, index, error)
        cost.append(count)
        for key in tracking.used:
            usage[key].add(index)
    lookup = {q: sorted(usage[q, 0] | usage[q, 1], key=lambda i: (cost[i], i)) for q in dead}
    result = dict(layout=str(layout), domain=domain, symbolic_fuel=fuel,
        scope='all pairs' if all_pairs else 'at least one changed decoder state',
        changed=sorted(changed, key=int), baseline_cases=len(checker.cases),
        protected_rows=42, fixed_dispatch=96, families={}, survivors=[])
    output.parent.mkdir(parents=True, exist_ok=True)
    for family in ('uniform', 'mixed'):
        group = dict(recipes=0, checks=0, full_checks=0, failures=Counter())
        result['families'][family] = group
        for deleted in dead:
            for keep in states:
                if keep == deleted or (not all_pairs and deleted not in changed and keep not in changed):
                    continue
                for bit in ([None] if family == 'uniform' else [0, 1]):
                    if bit is not None:
                        if keep == '96' or (keep, bit) in PROTECTED:
                            continue
                        if keep in dead and int(keep) < int(deleted):
                            continue
                        if table[deleted, bit] == table[keep, bit]:
                            continue
                    candidate = {(q, b): (w, d, keep if t == deleted else t)
                        for (q, b), (w, d, t) in table.items() if q != deleted}
                    if bit is not None:
                        w, d, target = table[deleted, bit]
                        candidate[keep, bit] = (w, d, keep if target == deleted else target)
                    assert len(candidate) == 490
                    checker.require_macro_support(candidate)
                    affected = lookup[deleted] if bit is None else sorted(
                        set(lookup[deleted]) | usage[keep, bit], key=lambda i: (cost[i], i))
                    failure = None
                    error = None
                    for index in affected:
                        group['checks'] += 1
                        ok, count, error = checker.check(candidate, index, fuel)
                        if not ok:
                            failure = index
                            break
                    if failure is None:
                        for index in range(len(checker.cases)):
                            group['full_checks'] += 1
                            ok, count, error = checker.check(candidate, index, fuel)
                            if not ok:
                                failure = index
                                break
                    group['recipes'] += 1
                    if failure is not None:
                        group['failures'][error] += 1
                        continue
                    name = f'layout{layout}_{domain}_{family}_{deleted}_{keep}_{bit}'
                    destination = output.parent / (name + '.tm')
                    destination.write_text('#! start 95\n' + ''.join(
                        f'{q} {b} {w} {d} {t}\n' for (q, b), (w, d, t) in sorted(
                        candidate.items(), key=lambda item: (int(item[0][0]), item[0][1]))))
                    found = dict(name=name, deleted=int(deleted), retained=int(keep),
                                 copied_read=bit, table=destination.name, blank_bootstrap_verified=False)
                    result['survivors'].append(found)
                    print('SURVIVOR', json.dumps(found), flush=True)
        print(layout, domain, family, json.dumps(group), flush=True)
        output.write_text(json.dumps(result, indent=2) + '\n')
    result['status'] = 'COMPLETE'
    output.write_text(json.dumps(result, indent=2) + '\n')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('layouts', nargs='+')
    parser.add_argument('--domain', choices=('unrestricted', 'product'), default='unrestricted')
    parser.add_argument('--all-pairs', action='store_true')
    parser.add_argument('--fuel', type=int, default=1500)
    parser.add_argument('--output-dir', type=Path, default=OUTPUT / 'folds')
    args = parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    for layout in args.layouts:
        run(layout, args.domain, args.all_pairs, args.fuel,
            args.output_dir / (f'layout{layout}-{args.domain}.json'))


if __name__ == '__main__':
    main()
