#!/usr/bin/env python3
"""Independently reconstruct the finite family and audit its complete ledger.

This checks partition/coverage and recorded outcomes, not symbolic traces.
It intentionally does not import the search driver or its pair generator.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent


def audit(table_path, ledger_path, result_path):
    raw = table_path.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '939f99d602c8f7057517c4369279de99e30827050fc743581df83f26aaf1b713'
    table = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        table[key] = int(write), direction, int(target)
    states = sorted({q for q, _ in table})
    assert len(states) == 252 and len(table) == 504 and 254 not in states
    boxes = {0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
    protected = {(q, bit) for q in boxes for bit in (0, 1)} - {(3, 0)}
    assert len(protected) == 55
    excluded = {96} | {q for q, _ in protected} | {table[k][2] for k in protected}
    eligible = set(states) - excluded
    pairs = []
    for dead in sorted(eligible):
        for keep in states:
            if dead == keep or keep == 96 or (keep in eligible and dead > keep):
                continue
            quotient = lambda row: (row[0], row[1], keep if row[2] == dead else row[2])
            for common_bit in (0, 1):
                disputed = 1 - common_bit
                if (keep, disputed) in protected:
                    continue
                same = quotient(table[dead, common_bit]) == quotient(table[keep, common_bit])
                different = quotient(table[dead, disputed]) != quotient(table[keep, disputed])
                if same and different:
                    pairs.append((dead, keep, disputed))
    assert len(pairs) == 264 and len(set(pairs)) == 264
    recorded = json.loads(result_path.read_text())
    assert recorded['status'] == 'completed' and not recorded['survivors']
    assert recorded['excluded_source_cases'] == []
    reasons = Counter()
    phase_first = []
    count = 0
    six = {8202, 8203, 8204, 8358, 8359, 8360}
    with ledger_path.open() as ledger:
        for index, (dead, keep, bit) in enumerate(pairs):
            group_reasons = Counter()
            group = recorded['groups'][index]
            assert (group['dead'], group['keep'], group['bit']) == (dead, keep, bit)
            assert group['checked'] == 1008
            for write in (0, 1):
                for direction in ('L', 'R'):
                    for target in [q for q in states if q != dead] + [254]:
                        line = ledger.readline()
                        assert line, ('missing ledger row', count)
                        row = json.loads(line)
                        assert len(row) == 8
                        assert row[:6] == [dead, keep, bit, write, direction, target], ('recipe mismatch', count)
                        failed, reason = row[6:]
                        assert isinstance(failed, int) and 0 <= failed < 8391
                        assert reason in {'unsupported', 'fuel', 'missing_transition'}
                        reasons[reason] += 1
                        group_reasons[reason] += 1
                        if failed in six:
                            phase_first.append(row)
                        count += 1
            assert dict(group_reasons) == group['failures']
        assert not ledger.read(), 'unexpected extra ledger rows'
    digest = hashlib.sha256(ledger_path.read_bytes()).hexdigest()
    assert len(recorded['groups']) == 264
    assert count == recorded['checked'] == recorded['planned'] == 266112
    assert dict(reasons) == recorded['reasons']
    assert digest == recorded['journal_sha256'] == '60e7a44066339e0979cb4ad172c0f0368812fe305fbfa1b928262da40946d690'
    assert len(phase_first) == 1674
    return {'scope': __doc__, 'status': 'PASS', 'recipes': count, 'pairs': len(pairs),
            'reasons': dict(reasons), 'phase_excluded_first_failures': phase_first,
            'journal_sha256': digest}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--table', type=Path, default=HERE/'inputs/permutation252.tm')
    parser.add_argument('--ledger', type=Path, default=HERE/'evidence/fusion-clean.jsonl')
    parser.add_argument('--result', type=Path, default=HERE/'evidence/fusion-clean.json')
    parser.add_argument('--output', type=Path, default=HERE/'evidence/coverage-recheck.json')
    args = parser.parse_args()
    assert __debug__, 'Run without -O: assertions are verification conditions.'
    result = audit(args.table, args.ledger, args.result)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print({k: v for k, v in result.items() if k != 'phase_excluded_first_failures'})


if __name__ == '__main__':
    main()
