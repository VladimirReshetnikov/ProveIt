#!/usr/bin/env python3
"""Optional bounded, exhaustive one-state-fold search around decoder256.tm.

Filters candidates using exactly the affine cases that visit the removed state.
Excluded source states are the register-box states, dispatch root, and the two
original bootstrap-sharing states 5 and 8. This is not a minimality proof.
"""
from pathlib import Path
import collections
import json
import sys
import time

HERE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(HERE))
import verify

table, _ = verify.load(HERE / 'machines/decoder256.tm')
saved = sys.argv
sys.argv = ['symexec.py', str(HERE / 'machines/baseline254.tm'), str(HERE), '40']
env = {}
exec((HERE / 'vendor/symexec.py').read_text().split('paths = json.load')[0], env)
sys.argv = saved
cases = []
for path, op in verify.paths_from_dag('candidate202.json'):
    branches = [('-', None)] if op == 'halt' else (
        [('z', 'dec0'), ('p', 'dec')] if op.endswith('.decnz') else
        [('-', 'inc' if op.endswith('.inc') else None)])
    for branch, effect in branches:
        if op.endswith('.inc') or (op.endswith('.decnz') and branch == 'p'):
            successor = env['inc'](path)
        elif op.endswith('.decnz'):
            successor = env['inc'](env['strip']('0', 1, path))
        elif op.startswith('_continue'):
            successor = env['strip']('1', int(op.split('.')[1]), path)
        elif op.startswith('_break'):
            successor = env['inc'](env['strip']('0', int(op.split('.')[1]), path))
        else:
            successor = ''
        effects = () if effect is None else ((effect, env['REG'][op.split('.')[1]]),)
        expected = (env['canon']([('b', 1)], [('r', 0, 1, 41), ('b', 1),
                    ('box', ('plain',) + effects)]) if successor is None else
                    env['canon']([('b', 1)], env['tape_R'](successor, 0, effects)))
        cases.append((path, op, branch, expected))


def check(index, current):
    path, op, branch, expected = cases[index]
    traced = verify.TracingTable(current)
    env['T'] = traced
    try:
        out = env['run']('96', [('b', 1)], env['tape_R'](path, 0, ()),
                         branch, expected, fuel=500)
        good = out[0] == ('halt' if op == 'halt' else 'ok')
        steps = out[1]
    except Exception:
        good, steps = False, 1000
    return good, steps, traced.used


usage = collections.defaultdict(list)
for index in range(len(cases)):
    ok, steps, trace = check(index, table)
    assert ok
    for state in {q for q, _ in trace}:
        usage[state].append((steps, index))
for states_cases in usage.values():
    states_cases.sort()
states = {q for q, _ in table}
protected = {str(q) for q in verify.BOX_STATES} | {'96', '5', '8'}
survivors = []
tested = 0
begin = time.monotonic()
for dead in sorted(states - protected, key=lambda q: (len(usage[q]), int(q))):
    for replacement in sorted(states - {dead}, key=int):
        candidate = {(q, b): (w, d, replacement if n == dead else n)
                     for (q, b), (w, d, n) in table.items() if q != dead}
        if all(check(i, candidate)[0] for _, i in usage[dead]):
            survivors.append([dead, replacement])
        tested += 1
    print('source', dead, '; tested', tested, '; survivors', len(survivors), flush=True)
result = {'tested': tested, 'survivors': survivors, 'elapsed_seconds': time.monotonic()-begin,
          'gap_lower_bound': 40, 'fuel_limit_per_case': 500,
          'excluded_source_states': sorted(protected, key=int),
          'status': 'bounded search, not a semantic minimality proof'}
(HERE / 'results/fold_search.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
