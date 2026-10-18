#!/usr/bin/env python3
"""Independent sampled replay of C++ stops using original Python rules.

Selects 32 reservoir samples per deleted state (fixed random seed), then
replays the exact reported failure case.  This complements full partition
replay; it is explicitly not a replay of every search diagnostic.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import random
import sys
from types import SimpleNamespace

class NeedAction(Exception):
    pass

class Partial(dict):
    def __init__(self, rows, pending):
        super().__init__(rows)
        self.pending = pending
    def __getitem__(self, key):
        if key in self.pending:
            raise NeedAction(key)
        return super().__getitem__(key)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, required=True)
    ap.add_argument('--machine-work', type=Path, required=True)
    ap.add_argument('--output', type=Path, required=True)
    args = ap.parse_args()
    work = args.machine_work
    source = args.repo / 'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/27-variant-experiments-machine_search-grammar_search-strict_affine.py'
    sys.modules['cost_search'] = SimpleNamespace()
    spec = importlib.util.spec_from_file_location('replay_strict', source)
    strict = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(strict)
    rows = {}
    raw = (work / 'action_data/baseline.tm').read_bytes()
    for line in raw.decode().splitlines():
        if line and not line.startswith('#'):
            q, b, w, d, t = line.split()
            rows[q, int(b)] = int(w), d, t
    families = {}
    for line in (work / 'action_data/family.tsv').read_text().splitlines():
        q, a, b, c, d, *_ = map(int, line.split())
        families[q] = [(str(a), b), (str(c), d)]
    cases = []
    for line in (work / 'action_data/cases.tsv').read_text().splitlines():
        p, r, z, halt, nxt, gap, effect, er, cost = line.split()
        if nxt == '_':
            nxt = ''
        eff = None if effect == '0' else ('inc' if effect == '2' else 'dec', int(er))
        target = strict.canon([('b', 1)], [('b', int(b)) for b in nxt] +
                              [('r', 0, 1, int(gap) - len(nxt)), ('b', 1), ('box', ('plain', eff))])
        guard = None if int(r) < 0 else (int(r), bool(int(z)))
        cases.append((p, guard, target, bool(int(halt))))
    rng = random.Random(20261017)
    samples = defaultdict(list)
    seen = Counter()
    ledger = work / 'all_actions.ledger.tsv'
    with ledger.open() as stream:
        next(stream)
        for line_no, line in enumerate(stream, 2):
            group, dead, a0, a1, outcome, case, reason, weight = line.split()
            if outcome != 'prune':
                continue
            dead = int(dead)
            seen[dead] += 1
            entry = (line_no, dead, int(a0), int(a1), int(case), int(reason), int(weight))
            if len(samples[dead]) < 32:
                samples[dead].append(entry)
            else:
                j = rng.randrange(seen[dead])
                if j < 32:
                    samples[dead][j] = entry
    checked = []
    reason_counts = Counter()
    action_changes = Counter()
    for dead in sorted(samples):
        destinations = [str(q) for q in range(255) if q != dead and ((str(q), 0) in rows or q == 254)]
        assert len(destinations) == 252
        options = [(w, d, t) for w in (0, 1) for d in ('R', 'L') for t in destinations]
        for line_no, _, a0, a1, case, reason, weight in sorted(samples[dead]):
            mutant = {k: v for k, v in rows.items() if k[0] != str(dead)}
            pending = set()
            for key, action in zip(families[dead], (a0, a1)):
                if action < 0:
                    pending.add(key)
                else:
                    new = options[action]
                    action_changes['different_write'] += new[0] != rows[key][0]
                    action_changes['different_move'] += new[1] != rows[key][1]
                    action_changes['halt_target'] += new[2] == '254'
                    mutant[key] = new
            p, guard, target, halt = cases[case]
            try:
                strict.run(Partial(mutant, pending), p, guard, target, halt=halt, fuel=1000)
            except NeedAction:
                raise AssertionError(('failure depends on unassigned row', line_no))
            except KeyError:
                observed = 4
            except AssertionError as exc:
                msg = str(exc)
                if msg == 'symbolic fuel exhausted':
                    observed = 1
                elif 'unknown left-run length' in msg or 'unknown right-run length' in msg:
                    observed = 2
                elif 'no justified box operation' in msg:
                    observed = 3
                else:
                    observed = 5
            else:
                raise AssertionError(('recorded failure passed original checker', line_no))
            assert observed == reason, (line_no, observed, reason)
            reason_counts[str(observed)] += 1
            checked.append({'ledger_line': line_no, 'deleted': dead, 'actions': [a0, a1],
                            'case': case, 'reason': observed, 'pruned_weight': weight})
    result = {'status': 'PASS', 'seed': 20261017, 'samples_per_group': 32,
              'groups': len(samples), 'sampled_failures': len(checked),
              'failure_reason_counts': dict(reason_counts), 'action_changes': dict(action_changes),
              'source27_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'ledger_sha256': hashlib.sha256(ledger.read_bytes()).hexdigest(),
              'checked': checked,
              'scope': 'All sampled diagnostic failures match original Python, without accessing pending actions. Sampling is not exhaustive failure replay or a semantic impossibility proof.'}
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'checked'}, indent=2))

if __name__ == '__main__':
    main()
