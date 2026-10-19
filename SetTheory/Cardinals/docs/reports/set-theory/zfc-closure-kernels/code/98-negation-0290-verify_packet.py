#!/usr/bin/env python3
"""Verify the retained research packet without modifying its delivered files.

Python 3.10+ standard library. The default checks source identities, the main
retained grammar witnesses, exact machine re-emission, pointers and
blank initialization. --full-runtime repeats the all-values runtime proof;
--church-search repeats the 7,500-trial coarse compiler controls as well.
"""
from pathlib import Path
from functools import cache
import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    if not __debug__:
        raise SystemExit('Assertions are verification gates; run without -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True,
                    help='A new directory outside this packet.')
    ap.add_argument('--full-runtime', action='store_true')
    ap.add_argument('--church-search', action='store_true')
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    out = args.output.resolve()
    if out.exists() or out.is_relative_to(root):
        raise SystemExit('Choose a new output directory outside the packet.')
    out.mkdir(parents=True)
    env = os.environ.copy()
    env['PYTHONDONTWRITEBYTECODE'] = '1'
    sys.dont_write_bytecode = True
    records = []

    def record(name, **details):
        records.append(dict(name=name, status='PASS', **details))
        (out/'reproduction.json').write_text(json.dumps(
            dict(status='IN_PROGRESS', checks=records), indent=2)+'\n')
        print('PASS', name, flush=True)

    def run(name, script, *params):
        command = [sys.executable, '-B', str(script), *map(str, params)]
        log = out/(name+'.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=out, env=env,
                                    stdout=stream, stderr=subprocess.STDOUT)
        if result.returncode:
            raise SystemExit(f'{name} failed; see {log}')
        record(name, argv=command, log=log.name)

    manifest = json.loads((root/'MANIFEST.json').read_text())
    for item in manifest['files']:
        p = root/item['path']
        assert p.is_file() and p.stat().st_size == item['bytes'], item['path']
        assert digest(p) == item['sha256'], item['path']
    record('payload-manifest', files=len(manifest['files']))

    fine = root/'dependencies/fine_grammar'
    source_path = fine/'runtime/inputs/closed-sequence-grammar-next22.json'
    source = json.loads(source_path.read_text())
    extracted = json.loads((root/'work/theory/fine_source_ast.json').read_text())
    assert extracted['ast_dag'] == source['ast_dag']
    assert extracted['source_sha256'] == digest(source_path)
    dag = source['ast_dag']
    @cache
    def bounds(i):
        row = dag[i]
        if row[0] == 'L':
            op, *args = row[1]
            return ((1,0) if op == 'dec' else (args[0],0) if op == 'brk'
                    else (0,args[0]) if op == 'cont' else (0,0))
        left, right = map(bounds, row[1:])
        return max(left[0]-1,right[0],0), max(left[1],right[1]-1,0)
    @cache
    def factors(i):
        row = dag[i]
        if row[0] == 'N' and bounds(row[1]) == bounds(row[2]) == (0,0):
            return factors(row[1])+factors(row[2])
        return (i,)
    atoms = sorted({i for item in source['atoms'].values()
                    for i in factors(item['ast'])})
    alphabet = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789'
    assert {alphabet[j]:i for j,i in enumerate(atoms)} == extracted['token_ast']
    encode = {i:alphabet[j] for j,i in enumerate(atoms)}
    root76 = ''.join(encode[i] for i in factors(source['sequence_ast_roots']['76']))
    assert root76 == extracted['root76']
    @cache
    def occurrences(i, target):
        row = dag[i]
        return int(i == target) + (sum(occurrences(j,target) for j in row[1:])
                                  if row[0] == 'N' else 0)
    ax_root = source['sequence_ast_roots']['76']
    assert occurrences(source['original_ast'], ax_root) == 1
    for target in (112,113):
        assert occurrences(source['original_ast'], target) == 30
        assert occurrences(ax_root, target) == 30
    record('theory-to-pinned-source-AST')

    # The component audits intentionally regenerate their JSON records.
    # Copy this small lane so those writes cannot alter delivered evidence.
    theory_copy = out/'theory-replay'
    shutil.copytree(root/'work/theory', theory_copy,
                    ignore=shutil.ignore_patterns('__pycache__','*.pyc'))
    run('theory-identities', theory_copy/'verify_packet.py',
        *(['--church-search'] if args.church_search else []))

    grammar = root/'work/grammar'
    run('frozen-control-grammar', grammar/'audit_lm_grammar.py',
        '--candidate', grammar/'lm-control/grammar.json',
        '--backend', grammar/'lm-backend/backend.json', '--fine', fine,
        '--output', out/'frozen-control-grammar.json')
    for name, backend in [('lm-warm','lm-backend'),
                          ('lm-dne32-warm','lm-dne32-backend'),
                          ('lm-church8-repaired','lm-church8-backend')]:
        choices = sorted((grammar/name).glob('search*.json'))
        assert choices, name
        for i, candidate in enumerate(choices):
            run(f'{name}-grammar-{i}', grammar/'audit_lm_grammar.py',
                '--candidate', candidate, '--backend',
                grammar/backend/'backend.json', '--fine', fine,
                '--output', out/f'{name}-grammar-{i}.json')
    run('routing-collection-regression', grammar/'audit_router_collection.py',
        '--output', out/'routing-collection-regression.json')
    run('trace-ideal-grammar', grammar/'audit_trace_ideal.py',
        '--candidate', grammar/'dne32/search0.json',
        '--inputs', grammar/'dne32', '--fine', fine,
        '--output', out/'trace-ideal-grammar.json')

    shadow = root/'work/terminal_shadow'
    spec = importlib.util.spec_from_file_location(
        'ordered_input_audit', shadow/'audit_grammar_input.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    checks = []
    for d in sorted((shadow/'seeds').glob('shadow-*')):
        checks.append(module.audit(d/'grammar.txt',
            root/'dependencies/canonical_inputs/canonical-constraints.txt',
            root/'dependencies/canonical_inputs/canonical-lock54.txt',
            d/'candidate.json'))
    for d in sorted((shadow/'partial-neg-seeds').glob('mask*')):
        if (d/'candidate.json').exists():
            checks.append(module.audit(d/'grammar.txt', d/'constraints.txt',
                fine/'fine-lock54.txt', d/'candidate.json'))
    assert len(checks) == 22
    (out/'ordered-grammar-audits.json').write_text(json.dumps(checks,indent=2)+'\n')
    record('ordered-grammar-witnesses', trials=len(checks))

    machine = out/'emitted-control'
    run('emit-exact-control', grammar/'emit_lm_machine.py',
        '--candidate', grammar/'lm-control/grammar.json', '--backend',
        grammar/'lm-backend/backend.json', '--fine', fine, '--output', machine)
    same = ['machine.tm','machine_old.tm','sites_logical.json',
            'sites_physical.json','allocation.json','renumbering.json',
            'register_bisimulation.json','blank_boot.json']
    for name in same:
        assert (machine/name).read_bytes() == (grammar/'lm-control'/name).read_bytes(), name
    before = json.loads((grammar/'lm-control/modified_source.json').read_text())
    after = json.loads((machine/'modified_source.json').read_text())
    assert all(before[key] == after[key] for key in before)
    record('byte-identical-control-reemission', files=same)

    runtime = root/'work/runtime'
    if args.full_runtime:
        run('all-values-runtime', runtime/'validate_emitted.py',
            '--runtime', fine/'runtime', '--machine', machine,
            '--output', out/'runtime-replay', '--padding', 64)
    else:
        run('independent-pointers-and-blank', runtime/'audit_frame_dynamic.py',
            '--old-table', machine/'machine_old.tm', '--table', machine/'machine.tm',
            '--renumbering', machine/'renumbering.json',
            '--logical-sites', machine/'sites_logical.json',
            '--physical-sites', machine/'sites_physical.json',
            '--bootstrap', machine/'blank_boot.json', '--padding', 64,
            '--whole-frame-report', runtime/'lm-control-validation/whole-frame.json',
            '--output', out/'independent-frame-audit.json')
    run('exact-state-graph', runtime/'audit_graph.py',
        machine/'machine_old.tm', out/'graph-audit.json')
    result = dict(status='PASS', full_runtime_replayed=args.full_runtime,
                  church_search_replayed=args.church_search, checks=records,
                  scope='The report separates source proofs, finite grammar checks, '
                        'unbounded runtime certificates, and finite search rejections. '
                        'No sub-245 machine or new proof-assistant endpoint is claimed.')
    (out/'reproduction.json').write_text(json.dumps(result,indent=2)+'\n')
    print('PASS complete requested packet replay', flush=True)


if __name__ == '__main__':
    main()
