#!/usr/bin/env python3
"""Audit the complete direct255 family and preservation of its recorded prefix.

This independent reconstruction checks recipes, coverage, recorded outcomes,
and the exact prefix bytes. It does not replay symbolic traces. The original
219,939 failed records were preserved; the continuation newly checked only
60,561 recipes. See resume_direct255_prefix.py for that continuation.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=HERE/'evidence/direct255-coverage.json')
    args = parser.parse_args()
    assert __debug__
    raw = (HERE/'inputs/direct255.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '120fb2885194f45b08c8586161683bab103e506d3d3db6f71a3634a024e2ebc8'
    table = {}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'): continue
        q, bit, write, direction, target = line.split()
        key = int(q), int(bit)
        assert key not in table
        table[key] = int(write), direction, int(target)
    states = sorted({q for q, bit in table})
    assert len(states) == 255 and len(table) == 510 and 254 not in states
    assert set(table) == {(q, bit) for q in states for bit in (0, 1)}
    assert all(w in (0, 1) and d in ('L', 'R') and t in set(states) | {254} for w, d, t in table.values())
    boxes = {0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}
    protected = {(q, bit) for q in boxes for bit in (0, 1)} - {(3, 0)}
    forbidden = {96, 64} | {q for q, bit in protected} | {table[k][2] for k in protected}
    eligible = set(states) - forbidden
    pairs = []
    for dead in sorted(eligible):
        for keep in states:
            if dead == keep or keep == 96 or (keep in eligible and dead > keep): continue
            quotient = lambda row: (row[0], row[1], keep if row[2] == dead else row[2])
            for bit in (0, 1):
                if (keep, 1-bit) in protected: continue
                if quotient(table[dead, bit]) == quotient(table[keep, bit]) and quotient(table[dead, 1-bit]) != quotient(table[keep, 1-bit]):
                    pairs.append((dead, keep, 1-bit))
    pairs.sort(key=lambda p: (max(p[:2]) < 254, *p))
    assert len(pairs) == len(set(pairs)) == 275
    summary = json.loads((HERE/'evidence/direct255-search.json').read_text())
    assert summary['status'] == 'completed' and not summary['survivors']
    prefix_raw = (HERE/'evidence/direct255-original-prefix.jsonl').read_bytes()
    prefix_digest = hashlib.sha256(prefix_raw).hexdigest()
    assert prefix_digest == summary['old_ledger_sha256'] == 'e4dec7fcf81b7b635e73fc2fc0e17724786257b98712d8606e88a0ffe723362d'
    prefix_lines = prefix_raw.splitlines(keepends=True)
    assert len(prefix_lines) == 219940
    prefix = [json.loads(line) for line in prefix_lines[:-1]]
    assert len(prefix) == summary['prefix_recipes_audited'] == 219939
    try: json.loads(prefix_lines[-1])
    except ValueError: pass
    else: raise AssertionError('Expected one malformed final prefix line, excluded from coverage')
    ledger_path = HERE/'evidence/direct255-ledger.jsonl'
    ledger_raw = ledger_path.read_bytes()
    assert ledger_raw.startswith(b''.join(prefix_lines[:-1])), 'Recorded prefix bytes must remain exact'
    digest = hashlib.sha256(ledger_raw).hexdigest()
    assert digest == summary['ledger_sha256'] == '3891d8532b0ebe2bd178e14fc94cd09bbffb8da89dc3c4b8b95f47ed41db1f0a'
    count = 0
    reasons = Counter()
    with ledger_path.open() as ledger:
        for dead, keep, bit in pairs:
            targets = [q for q in states if q != dead] + [254]
            all_actions = [(w, d, t) for w in (0, 1) for d in ('L', 'R') for t in targets]
            quotient = lambda row: (row[0], row[1], keep if row[2] == dead else row[2])
            originals = [quotient(table[dead, bit]), quotient(table[keep, bit])]
            actions = originals + [a for a in all_actions if a not in originals]
            assert len(actions) == len(set(actions)) == 1020
            for write, direction, target in actions:
                line = ledger.readline()
                assert line, ('missing recipe', count)
                row = json.loads(line)
                assert len(row) == 8 and row[:6] == [dead, keep, bit, write, direction, str(target)], ('wrong recipe', count)
                assert isinstance(row[6], int) and 0 <= row[6] < 7311
                assert row[7] in {'fuel', 'unsupported', 'missing_transition'}
                if count < len(prefix): assert row == prefix[count]
                reasons[row[7]] += 1
                count += 1
        assert not ledger.read(), 'unexpected extra recipes'
    assert count == summary['checked'] == summary['planned'] == 280500
    assert count - len(prefix) == summary['new_recipes'] == 60561
    assert dict(reasons) == summary['reasons']
    result = {'scope': __doc__, 'status': 'PASS', 'pairs': len(pairs), 'recipes': count,
              'recorded_prefix_recipes_structurally_audited': len(prefix), 'recorded_prefix_bytes_preserved': True,
              'malformed_partial_line_excluded': True, 'newly_evaluated_recipes_in_continuation': 60561,
              'new_case_checks_in_continuation': summary['new_case_checks'],
              'symbolic_traces_replayed_by_this_coverage_audit': 0,
              'survivors': 0, 'reasons': dict(reasons), 'ledger_sha256': digest,
              'recorded_prefix_sha256': prefix_digest}
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(result)


if __name__ == '__main__': main()
