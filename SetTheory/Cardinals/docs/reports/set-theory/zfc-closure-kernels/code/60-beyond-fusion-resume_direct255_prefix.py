#!/usr/bin/env python3
"""Continue only the unread suffix of a structurally audited failed-recipe prefix."""
from pathlib import Path
from collections import Counter, defaultdict
import argparse
import hashlib
import json
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import verify_runtime as v


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--seconds', type=float, default=900)
    parser.add_argument('--output-directory', type=Path, default=HERE/'direct255-resume-recheck')
    args = parser.parse_args()
    assert __debug__ and args.seconds > 0
    strict = v.load_strict()
    path = HERE/'inputs/direct255.tm'
    assert hashlib.sha256(path.read_bytes()).hexdigest() == '120fb2885194f45b08c8586161683bab103e506d3d3db6f71a3634a024e2ebc8'
    numeric = v.audit.read_table(path.read_bytes())
    table = {(str(q), b): (w, d, str(t)) for (q, b), (w, d, t) in numeric.items()}
    _, _, cases = v.cases_from_dag(json.loads((HERE/'inputs/direct_fused_dag.json').read_text()), strict)
    assert len(cases) == 7311
    class Tracking(dict):
        def __init__(self, t): super().__init__(t); self.used = set()
        def __getitem__(self, key): self.used.add(key); return super().__getitem__(key)
    def check(t, i):
        pc, op, logical, guard, nxt, goal = cases[i]
        try:
            counts, literal = strict.run(t, pc, guard, goal, halt=(op == 'CH'), fuel=1500)
            assert literal > 0
            return True, sum(counts.values()), None
        except AssertionError as error:
            return False, 0, 'fuel' if str(error) == 'symbolic fuel exhausted' else 'unsupported'
        except KeyError:
            return False, 0, 'missing_transition'
    usage, costs = defaultdict(set), {}
    for i in range(len(cases)):
        tracked = Tracking(table)
        ok, cost, _ = check(tracked, i)
        assert ok, i
        costs[i] = cost
        for key in tracked.used: usage[key].add(i)
    protected = {(str(q), b) for q, b in v.audit.BOX_PAIRS}
    states = sorted({q for q, b in table}, key=int)
    eligible = set(states) - ({'96', '64'} | {q for q, b in protected} | {table[k][2] for k in protected})
    pairs = []
    for q in sorted(eligible, key=int):
        for r in states:
            if q == r or r == '96' or (r in eligible and int(q) > int(r)): continue
            quotient = lambda row: (row[0], row[1], r if row[2] == q else row[2])
            for b in (0, 1):
                if (r, 1-b) not in protected and quotient(table[q, b]) == quotient(table[r, b]) and quotient(table[q, 1-b]) != quotient(table[r, 1-b]):
                    pairs.append((q, r, 1-b))
    pairs.sort(key=lambda x: (max(map(int, x[:2])) < 254, int(x[0]), int(x[1]), x[2]))
    assert len(pairs) == 275
    oldpath = HERE/'evidence/direct255-original-prefix.jsonl'
    raw = oldpath.read_bytes()
    assert hashlib.sha256(raw).hexdigest() == 'e4dec7fcf81b7b635e73fc2fc0e17724786257b98712d8606e88a0ffe723362d'
    oldlines = raw.splitlines(keepends=True)
    prefix = [json.loads(line) for line in oldlines[:-1]]
    assert len(prefix) == 219939
    try: json.loads(oldlines[-1])
    except ValueError: pass
    else: raise AssertionError('Expected exactly one truncated last line')
    outdir = args.output_directory
    outdir.mkdir(parents=True, exist_ok=True)
    ledger = outdir/'ledger.jsonl'
    result = {'scope': __doc__, 'status': 'running', 'pairs': len(pairs), 'planned': len(pairs)*4*len(states),
              'prefix_recipes_audited': len(prefix), 'old_ledger_sha256': hashlib.sha256(raw).hexdigest(),
              'checked': 0, 'new_recipes': 0, 'new_case_checks': 0, 'survivors': [], 'reasons': Counter()}
    began = time.monotonic()
    with ledger.open('w') as output:
        for q, r, bit in pairs:
            candidate = {k: (w, d, r if t == q else t) for k, (w, d, t) in table.items() if k[0] != q}
            affected = usage[q, 0] | usage[q, 1] | usage[r, bit]
            order = sorted(affected, key=lambda i: (costs[i], i))
            witnesses = []
            targets = [s for s in states if s != q] + ['254']
            allactions = [(w, d, t) for w in (0, 1) for d in ('L', 'R') for t in targets]
            original = [(w, d, r if t == q else t) for w, d, t in (table[q, bit], table[r, bit])]
            actions = original + [a for a in allactions if a not in original]
            assert len(actions) == 1020
            for action in actions:
                recipe = [int(q), int(r), bit, *action]
                index = result['checked']
                if index < len(prefix):
                    row = prefix[index]
                    assert row[:6] == recipe and isinstance(row[6], int) and 0 <= row[6] < 7311
                    assert row[7] in {'fuel', 'unsupported', 'missing_transition'}
                    failed, reason = row[6:]
                else:
                    candidate[r, bit] = action
                    assert all(candidate[k] == table[k] for k in protected)
                    failed, reason = None, None
                    for i in witnesses + [i for i in order if i not in witnesses]:
                        ok, _, reason = check(candidate, i); result['new_case_checks'] += 1
                        if not ok: failed = i; break
                    if failed is None:
                        for i in range(len(cases)):
                            ok, _, reason = check(candidate, i); result['new_case_checks'] += 1
                            if not ok: failed = i; break
                    result['new_recipes'] += 1
                    if failed is None:
                        entry = {'recipe': recipe, 'states': len(candidate)//2}
                        text = '#! start 64\n' + ''.join(f'{q0} {b} {w} {d} {t}\n' for (q0, b), (w, d, t) in sorted(candidate.items(), key=lambda x: (int(x[0][0]), x[0][1])))
                        dest = outdir/f'survivor-{len(result["survivors"])}.tm'
                        dest.write_text(text)
                        entry['table'] = str(dest)
                        entry['sha256'] = hashlib.sha256(text.encode()).hexdigest()
                        result['survivors'].append(entry)
                        print('SURVIVOR', entry, flush=True)
                    row = recipe + [failed, reason]
                output.write(json.dumps(row, separators=(',', ':')) + '\n')
                if failed is not None:
                    result['reasons'][reason] += 1
                    if failed not in witnesses: witnesses.insert(0, failed)
                result['checked'] += 1
            if result['new_recipes']:
                print('resumed recipes', result['new_recipes'], 'elapsed', round(time.monotonic()-began, 1), flush=True)
                if time.monotonic()-began > args.seconds:
                    result['status'] = 'partial'
                    break
        else:
            result['status'] = 'completed'
    result['ledger_sha256'] = hashlib.sha256(ledger.read_bytes()).hexdigest()
    result['elapsed_seconds'] = time.monotonic()-began
    (outdir/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    print(result, flush=True)


if __name__ == '__main__': main()
