#!/usr/bin/env python3
"""Replay either recorded finite source-contract screen; no new family is added.

The contract executor retains inherited register-box assumptions. A hypothetical
passing table that changed a protected box row would need an independent engine
proof and a complete startup check before acceptance. Both recorded screens have
zero passing tables, so no such candidate is asserted here.
"""
import argparse
import itertools
import json
from support import b, c, load


def mergers(rows, contracts):
    controls = sorted({q for q, bit in rows})
    protected = set(c.BOXSTATES) | {84}
    traces = {q: set() for q in controls}
    for i, contract in enumerate(contracts):
        seen = set()
        assert c.run(rows, contract, observe=lambda s: seen.add(s[0])) is not None
        for q in seen:
            traces[q].add(i)
    deleted = 302
    attempted = 0
    passed = []
    for kept in controls:
        if kept == deleted or kept in protected:
            continue
        for choices in itertools.product([0, 1], repeat=2):
            candidate = {key: (w, d, kept if n == deleted else n)
                         for key, (w, d, n) in rows.items() if key[0] != deleted}
            for bit in (0, 1):
                w, d, n = rows[(kept if choices[bit] else deleted), bit]
                candidate[kept, bit] = w, d, kept if n == deleted else n
            changed = []
            for q in (deleted, kept):
                if any(candidate[kept, bit] != (rows[q, bit][0], rows[q, bit][1],
                       kept if rows[q, bit][2] == deleted else rows[q, bit][2])
                       for bit in (0, 1)):
                    changed.append(q)
            relevant = sorted(set().union(*(traces[q] for q in changed)))
            attempted += 1
            if all(c.run(candidate, contracts[i]) is not None for i in relevant):
                passed.append({'deleted': deleted, 'kept': kept, 'row_choices': choices})
    assert attempted == 676
    return {'family': '302_mergers', 'attempted': attempted, 'passed': passed,
            'remaining_controls_per_choice': 169, 'row_choice_pairs': 4,
            'contract_count': len(contracts), 'executor_fuel': 1024}


def redirects(rows, contracts):
    baseline = c.validate(rows, contracts)
    assert baseline['ok']
    controls = sorted({q for q, bit in rows}) + [254]
    candidate = {key: act for key, act in rows.items() if key[0] != 302}
    assert [key for key, act in candidate.items() if act[2] == 302] == [(113, 0)]
    passed, attempted, best_count, best_action = [], 0, 0, None
    for w, d, n in itertools.product([0, 1], [False, True], controls):
        if n == 302:
            continue
        candidate[113, 0] = w, d, n
        done = 0
        for contract in contracts:
            if c.run(candidate, contract) is None:
                break
            done += 1
        attempted += 1
        if done > best_count:
            best_count, best_action = done, [w, 'R' if d else 'L', n]
        if done == len(contracts):
            passed.append([w, 'R' if d else 'L', n])
    assert attempted == 776
    return {'family': '113_0_redirects_after_deleting302', 'attempted': attempted,
            'passed': passed, 'best_completed_contracts': best_count,
            'best_action': best_action, 'baseline': baseline,
            'contract_count': len(contracts), 'executor_fuel': 1024}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('family', choices=['mergers', 'redirects'])
    args = parser.parse_args()
    rows, sites, cfg, contracts = load()
    result = mergers(rows, contracts) if args.family == 'mergers' else redirects(rows, contracts)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
