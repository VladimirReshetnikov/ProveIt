#!/usr/bin/env python3
"""Reproduce the literal-table audit using the pinned published affine model.

This is a Python verification experiment, NOT a new Coq certificate. The model
uses the pre-existing register-box contracts. See README.md for the boundary.
Only the Python standard library is needed. Run: python verify.py
"""
from pathlib import Path
import collections
import hashlib
import json
import sys

if not __debug__:
    raise SystemExit('Refusing optimized Python (-O/-OO): this audit requires enabled assertions.')

HERE = Path(__file__).resolve().parent
VENDOR_HASHES = {
    'symexec.py': '5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d',
    'tmlib.py': 'd66c407bfa9e78b01a3cd1f363beb3d68d6091eabc007caabc915ff972b4ca00',
}
BASE_HASH = 'd655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
for filename, digest in VENDOR_HASHES.items():
    assert hashlib.sha256((HERE / 'vendor' / filename).read_bytes()).hexdigest() == digest
assert hashlib.sha256((HERE / 'machines/baseline254.tm').read_bytes()).hexdigest() == BASE_HASH
sys.path.insert(0, str(HERE / 'vendor'))
from tmlib import load, Run

# Conservative superset of the states used inside the published box contracts.
# Dispatch root 96 is deliberately not here. At zero decrement the box contract
# exits in state 3 before executing its exterior read-0 transition.
BOX_STATES = {0, 1, 2, 3, 4, 6, 28, 31, 38, 40, 43, 44, 48, 56, 59, 60,
              63, 64, 69, 73, 75, 83, 85, 95, 97, 109, 112, 131}
BOX_PAIRS = {(str(q), b) for q in BOX_STATES for b in (0, 1)} - {('3', 0)}
REG_NAMES = ['nextproof', 'topwff', 'wffstack', 'axiomcode', 'param1',
             'param2', 'scratch1', 'scratch2', 'prooflist']
BASE, _ = load(HERE / 'machines/baseline254.tm')


def paths_from_dag(filename):
    obj = json.loads((HERE / 'data' / filename).read_text())
    nodes = {int(k): v for k, v in obj['nodes'].items()}
    paths = []
    def walk(e, prefix):
        k = e[0]
        if k == 'N':
            a, b = nodes[e[1]]
            walk(a, prefix + '0')
            walk(b, prefix + '1')
            return
        v = e[1] if len(e) > 1 else 0
        op = (f'3.{REG_NAMES[v]}.inc' if k == 'I' else
              f'3.{REG_NAMES[v]}.decnz' if k == 'D' else
              f'_break.{v}' if k == 'B' else
              f'_continue.{v}' if k == 'C' else 'halt')
        paths.append((prefix, op))
    walk(('N', obj['root']), '')
    return paths


class TracingTable(dict):
    def __init__(self, table):
        super().__init__(table)
        self.used = set()
    def __getitem__(self, key):
        self.used.add(key)
        return super().__getitem__(key)


def affine_audit(table, paths, gap):
    """All leaves, both decrement cases; symbolic free gap n >= 0."""
    for pair in BOX_PAIRS:
        assert table[pair] == BASE[pair], ('modified protected box row', pair)
    oldargv = sys.argv
    sys.argv = ['symexec.py', str(HERE / 'machines/baseline254.tm'), str(HERE), str(gap)]
    env = {}
    # Read only definitions, omitting the upstream command-line driver. The
    # exact upstream bytes are pinned above. Tracing wraps table lookup only.
    try:
        source = (HERE / 'vendor/symexec.py').read_text().split('paths = json.load')[0]
        exec(compile(source, str(HERE / 'vendor/symexec.py'), 'exec'), env)
    finally:
        sys.argv = oldargv
    traced = TracingTable(table)
    env['T'] = traced
    stats = collections.Counter()
    failures = []
    for path, op in paths:
        cases = [('-', None)] if op == 'halt' else (
            [('z', 'dec0'), ('p', 'dec')] if op.endswith('.decnz') else
            [('-', 'inc' if op.endswith('.inc') else None)])
        for branch, effect in cases:
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
            effect_data = () if effect is None else ((effect, env['REG'][op.split('.')[1]]),)
            if successor is None:
                expected = env['canon']([('b', 1)], [
                    ('r', 0, 1, gap + 1), ('b', 1), ('box', ('plain',) + effect_data)])
                tag = 'overflow'
            else:
                expected = env['canon']([('b', 1)], env['tape_R'](successor, 0, effect_data))
                tag = 'normal'
            stats['cases'] += 1
            try:
                out = env['run']('96', [('b', 1)], env['tape_R'](path, 0, ()),
                                 branch, expected, fuel=20000)
                assert out[0] == ('halt' if op == 'halt' else 'ok'), out
                stats['pass'] += 1
                stats['halt' if op == 'halt' else tag] += 1
                stats['abstract_steps_all_cases'] += out[1]
                if op != 'halt':
                    stats['abstract_steps_nonhalting_cases'] += out[1]
                    stats['max_abstract_steps'] = max(stats['max_abstract_steps'], out[1])
                    stats['max_root_visits'] = max(stats['max_root_visits'], out[2])
            except Exception as ex:
                failures.append({'path': path, 'operation': op, 'branch': branch,
                                 'error': repr(ex)})
    assert not failures, failures[:5]
    stats['gap_lower_bound'] = gap
    stats['path_depth'] = max(len(p) for p, _ in paths)
    return dict(stats), traced.used


def boot_audit(table):
    target = json.loads((HERE / 'data/blank_boot_target.json').read_text())
    run = Run(table, '0')
    used = set()
    for _ in range(target['steps']):
        used.add((run.state, run.tape.get(run.head, 0)))
        assert run.step(), 'halt during required initialization'
    assert run.state == target['state']
    assert run.head == target['head']
    assert [x - run.head for x in run.ones()] == target['ones_relative']
    return {'steps': run.t, 'head': run.head, 'state': run.state,
            'gap': target['gap'], 'exact_finite_tape_match': True}, used


def check_total_closed(table, start):
    states = {q for q, _ in table}
    assert start in states and '254' not in states
    assert len(table) == 2 * len(states)
    for q in states:
        for b in (0, 1):
            w, d, n = table[q, b]
            assert w in (0, 1) and d in ('L', 'R') and n in states | {'254'}
    return len(states)


def audit_file(filename, dag, gap, blank):
    table, start = load(HERE / 'machines' / filename)
    n = check_total_closed(table, start)
    stats, used = affine_audit(table, paths_from_dag(dag), gap)
    boot = None
    if blank:
        assert start == '0'
        boot, boot_used = boot_audit(table)
        used |= boot_used
    else:
        seed = json.loads((HERE / 'data/prepared252_seed.json').read_text())
        assert start == seed['state'] == '96'
    all_covered = used | BOX_PAIRS
    covered_states = {q for q, _ in all_covered} | {start, '96'}
    assert covered_states <= {q for q, _ in table}
    return {'working_states': n, 'transition_count': len(table), 'terminal_state': '254',
            'start_state': start, 'blank_tape': blank, 'total_and_target_closed': True,
            'sha256': hashlib.sha256((HERE / 'machines' / filename).read_bytes()).hexdigest(),
            'affine': stats, 'boot': boot,
            'oracle_protected_pairs': len(BOX_PAIRS),
            'coverage_pairs_including_oracles': len(all_covered)}, all_covered


def main():
    result = {'status': 'Python affine audit with existing register-box oracle contracts; no new kernel proof',
              'machines': {}}
    specs = [('baseline254.tm', 'decoder_entries.json', 40, True),
             ('prepared252.tm', 'decoder_entries.json', 40, False),
             ('decoder267.tm', 'candidate202.json', 41, True),
             ('decoder256.tm', 'candidate202.json', 41, True)]
    for filename, dag, gap, blank in specs:
        stats, covered = audit_file(filename, dag, gap, blank)
        result['machines'][filename] = stats
        print(filename, stats['working_states'], 'states;', stats['affine']['pass'],
              'affine cases; blank bootstrap', bool(stats['boot']), flush=True)
        (HERE / 'results' / (filename + '.coverage.json')).write_text(
            json.dumps(sorted(covered, key=lambda p: (int(p[0]), p[1])), indent=2) + '\n')
    (HERE / 'results/verification.json').write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    main()
