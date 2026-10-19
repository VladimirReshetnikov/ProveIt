#!/usr/bin/env python3
"""Portable finite replay and optional bounded grammar discovery campaigns.

Run from any working directory.  Defaults assume this folder is grammar/ in
the delivered research package.  Search products go to reproduced/, never
overwriting the recorded evidence.
"""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import time

from audit_search_outputs import audit
from audit_semantic_collisions import screen
from summarize_recorded import summarize

BASE = Path(__file__).resolve().parent


def run(command, cwd=None, log=None):
    if log is None:
        subprocess.run([str(x) for x in command], cwd=cwd, check=True)
    else:
        with Path(log).open('w') as stream:
            subprocess.run([str(x) for x in command], cwd=cwd, check=True,
                           stdout=stream, stderr=subprocess.STDOUT)


def stage(package, semantic, out):
    out.mkdir(parents=True, exist_ok=True)
    run([sys.executable, BASE / 'prepare_fine_inputs.py', '--package', package,
         '--output', out])
    affine = json.loads((semantic / 'affine_commutations.json').read_text())
    pairs = sorted(tuple(sorted(p)) for p in affine['independent_pairs'])
    assert len(pairs) == len(set(pairs)) == 178
    (out / 'affine-pairs.txt').write_text(
        '178\n' + '\n'.join(' '.join(p) for p in pairs) + '\n')
    for name in ('fine_milp.py', 'fine_milp_routes.py', 'phrase_flow_milp.py',
                 'parse_commuting_variants.py'):
        shutil.copyfile(BASE / name, out / name)


def verify(package, semantic, out):
    started = time.monotonic()
    manifest = json.loads((BASE / 'manifest.json').read_text())
    for name, digest in manifest['sha256'].items():
        assert hashlib.sha256((BASE / name).read_bytes()).hexdigest() == digest, name
    stage(package, semantic, out / 'inputs')
    text_inputs = (
        'route-grammar.txt', 'route-constraints.txt', 'bootstrap-lock54.txt',
        'bootstrap-lock50.txt', 'no-locks.txt', 'seed245.txt',
        'seed245-rotated-lastloop.txt', 'fine-route-grammar.txt',
        'fine-route-constraints.txt', 'fine-bootstrap-lock54.txt',
        'fine-seed245.txt', 'trace-grammar.txt', 'trace-seed245.txt',
        'trace-info.txt', 'affine-pairs.txt',
    )
    for name in text_inputs:
        actual = (out / 'inputs' / name).read_text().split()
        expected = (BASE / name).read_text().split()
        assert actual == expected, ('regenerated input differs', name)
    for name in ('fine_encoding.json', 'grammar245.json'):
        assert json.loads((out / 'inputs' / name).read_text()) == json.loads(
            (BASE / name).read_text()), name
    config = json.loads((BASE / 'search_profiles.json').read_text())
    results = []
    for profile in config['profiles']:
        result = audit(package, BASE / profile['output'], profile['domain'],
                       BASE / profile['audit_locks'], BASE / 'affine-pairs.txt')
        results.append(dict(file=profile['output'], **result))
    assert results == json.loads((BASE / 'independent_grammar_audits.json').read_text())
    control = audit(package, BASE / 'fine-milp16-control.json', 'fine',
                    BASE / 'bootstrap-lock54.txt')
    assert control == json.loads((BASE / 'milp_control_grammar_audit.json').read_text())
    collision = screen(package, semantic / 'affine_commutations.json')
    assert collision == json.loads((BASE / 'semantic_collision_audit.json').read_text())
    obstruction_path = out / 'locked_zero5_obstruction_verified.json'
    run([sys.executable, BASE / 'verify_zero5_lock_obstruction.py',
         '--package', package, '--grammar', package / 'grammar.json',
         '--output', obstruction_path], log=out / 'obstruction-replay.log')
    assert json.loads(obstruction_path.read_text()) == json.loads(
        (BASE / 'locked_zero5_obstruction_verified.json').read_text())
    summary = summarize(BASE)
    assert summary == json.loads((BASE / 'grammar_search_results.json').read_text())
    (out / 'independent_grammar_audits.json').write_text(json.dumps(results, indent=2) + '\n')
    report = {
        'status': 'PASS_FINITE_RESEARCH_REPLAY',
        'manifest_files_checked': len(manifest['sha256']),
        'annealing_outputs_checked': len(results),
        'milp_control_grammar_checked': True,
        'quotient_screens_replayed': 4,
        'locked_zero5_obstruction_checked': True,
        'recorded_summary_recomputed': True,
        'seconds': time.monotonic() - started,
        'scope': 'This replay checks finite artifacts, exact grammar equations, '
                 'source-path statistics and the explicit lock obstruction. '
                 'It does not re-prove the supplied affine source matrices, '
                 'certify MILP infeasibility, run discovery, or prove any new '
                 'binary-machine runtime or blank-start theorem.',
    }
    (out / 'verification-summary.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


def discovery(action, chosen, package, semantic, out, seconds):
    config = json.loads((BASE / 'search_profiles.json').read_text())
    if action == 'search':
        profiles = config['profiles']
    elif action == 'milp':
        profiles = config['milp']
    else:
        profiles = [{'name': 'adjacent'}, {'name': 'ranked'}]
    if chosen != 'all':
        profiles = [p for p in profiles if p['name'] == chosen]
    assert profiles, f'Unknown {action} profile: {chosen}'
    for profile in profiles:
        work = out / profile['name']
        stage(package, semantic, work)
        if action == 'search':
            exe = work / 'annealer'
            run(['g++', '-O3', '-std=c++17', BASE / profile['source'], '-o', exe])
            command = [exe, work / profile['grammar_input'],
                       work / profile['constraint_input'], work / profile['output'],
                       seconds if seconds is not None else profile['budget_seconds'],
                       profile['seed'], profile['stopcount'], work / profile['locks'],
                       work / profile['initial_seed']]
            if profile['domain'].endswith('trace'):
                command.append(work / 'trace-info.txt')
            if profile['domain'] == 'affine_trace':
                command.append(work / 'affine-pairs.txt')
            run(command, cwd=work, log=work / profile['log'])
            result = audit(package, work / profile['output'], profile['domain'],
                           work / profile['audit_locks'], work / 'affine-pairs.txt')
            (work / 'finite-audit.json').write_text(json.dumps(result, indent=2) + '\n')
        elif action == 'milp':
            command = [sys.executable, work / profile['source'],
                       '--maxlen', profile['maxlen'], '--bound', profile['bound'],
                       '--seconds', seconds if seconds is not None else profile['seconds'],
                       '--output', profile['output']]
            if profile.get('dynamic_routes'):
                command.append('--dynamic-routes')
            run(command, cwd=work, log=work / profile['log'])
        else:
            name = profile['name'] + '-parse-search'
            command = [sys.executable, work / 'parse_commuting_variants.py',
                       '--output', name + '.json']
            if profile['name'] == 'ranked':
                command += ['--variants', semantic / 'commuting_ax_variants.json']
            run(command, cwd=work, log=work / (name + '.log'))
        print(f'Completed {action} {profile["name"]}: {work}', flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=('verify', 'search', 'milp', 'parse', 'prepare'))
    p.add_argument('profile', nargs='?', default='all')
    p.add_argument('--package', type=Path, default=BASE.parent / 'reference/zfc245')
    p.add_argument('--semantic-root', type=Path, default=BASE.parent / 'semantic')
    p.add_argument('--output', type=Path)
    p.add_argument('--seconds', type=int, help='Override a discovery time budget.')
    a = p.parse_args()
    assert __debug__, 'Assertions must remain enabled.'
    package, semantic = a.package.resolve(), a.semantic_root.resolve()
    out = (a.output or BASE / 'reproduced' / a.action).resolve()
    out.mkdir(parents=True, exist_ok=True)
    if a.action == 'verify':
        verify(package, semantic, out)
    elif a.action == 'prepare':
        stage(package, semantic, out)
    else:
        discovery(a.action, a.profile, package, semantic, out, a.seconds)
