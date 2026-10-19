#!/usr/bin/env python3
"""Offline reproduction of the exact 242-state construction and its checks.

The local proof premises, finite runtime regressions, and optional bounded
discovery searches retain separate meanings in the resulting record.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def main():
    require(__debug__, 'Assertions must remain enabled; do not use -O.')
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--search', action='store_true')
    args = ap.parse_args()
    output = args.output.resolve()
    require(not output.exists(), 'Output must be a new directory.')
    require(ROOT not in output.parents, 'Use an output directory outside the package.')
    pins = json.loads((ROOT/'INPUTS.json').read_text())
    before = {}
    for item in pins['files']:
        p = ROOT/item['path']
        require(p.is_file() and not p.is_symlink(), 'Missing or linked input: '+str(p))
        require(digest(p) == item['sha256'], 'Changed input: '+str(p))
        before[item['path']] = digest(p)
    output.mkdir(parents=True)
    record = {'status':'RUNNING', 'search_requested':args.search,
              'input_pins_sha256':digest(ROOT/'INPUTS.json'),
              'input_hashes_before':before, 'commands':[],
              'scope':'Ordinary universal local-premise checks, independent finite '
                      'source fixtures and blank replay, separate equational '
                      'frontend checks, and optional restricted discovery search. '
                      'No proof-assistant or expanded baseline replay is performed.'}
    def save():
        (output/'verification.json').write_text(json.dumps(record,indent=2)+'\n')
    def run(label, script, argv):
        command = [sys.executable, '-I', '-B', str(ROOT/script), *map(str,argv)]
        started = time.monotonic()
        outlog, errlog = output/(label+'.stdout.log'), output/(label+'.stderr.log')
        with outlog.open('wb') as out, errlog.open('wb') as err:
            result = subprocess.run(command, cwd=output, stdout=out, stderr=err)
        record['commands'].append({'label':label, 'command':command,
            'exit_code':result.returncode, 'seconds':time.monotonic()-started,
            'stdout':{'path':outlog.name,'sha256':digest(outlog)},
            'stderr':{'path':errlog.name,'sha256':digest(errlog)}})
        save()
        require(result.returncode == 0, 'Check failed: '+label)
    save()
    try:
        baseline = ROOT/'baseline/zfc_combined243_old.tm'
        machine = ROOT/'machine'
        run('universal-transfer', 'code/prove_zero_reuse242.py',
            [baseline, '--output', output/'regenerated-machine'])
        for name in ('zfc_zero_reuse242.tm','zfc_zero_reuse242_old.tm','renumbering.json'):
            require((machine/name).read_bytes() == (output/'regenerated-machine'/name).read_bytes(),
                    'Regenerated artifact differs: '+name)
        run('independent-runtime', 'code/verify_candidate.py',
            ['--table',machine/'zfc_zero_reuse242_old.tm',
             '--canonical',machine/'zfc_zero_reuse242.tm','--baseline',baseline,
             '--sites',ROOT/'baseline/sites_logical.json',
             '--output',output/'independent-verification.json'])
        runtime = json.loads((output/'independent-verification.json').read_text())
        require(runtime['status']=='PASS' and runtime['working_states']==242,
                'Independent runtime status')
        cases = runtime['literal_fixtures']
        require((cases['guarded_cases'],cases['total_transitions'],cases['covered_rows'])
                == (8390,6473406,484) and cases['unused_rows']==[], 'Runtime census')
        require(runtime['blank']['candidate_steps']==407979 and
                runtime['blank']['baseline_steps']==407967 and
                runtime['blank']['sparse_dense_agreement'], 'Blank replay census')
        run('printed-table', 'code/render_table.py', ['--check'])
        run('stack-kernel', 'research/stack-kernel/stack_kernel.py',
            ['--out',output/'stack-kernel'])
        for p in sorted((ROOT/'research/stack-kernel/generated').iterdir()):
            if p.is_file():
                require(p.read_bytes() == (output/'stack-kernel'/p.name).read_bytes(),
                        'Equational frontend regeneration differs: '+p.name)
        if args.search:
            for count, table in ((243,baseline),(242,machine/'zfc_zero_reuse242_old.tm')):
                result_path = output/f'contextual-search{count}.json'
                run(f'discovery-{count}','code/search_contextual_folds.py',
                    [table,'--output',result_path])
                actual = json.loads(result_path.read_text())
                expected = json.loads((ROOT/f'research/contextual-search/contextual-search{count}.json').read_text())
                actual.pop('elapsed_seconds'); expected.pop('elapsed_seconds')
                require(actual == expected, f'Restricted search differs: {count}')
        record['input_hashes_after'] = {p:digest(ROOT/p) for p in before}
        require(record['input_hashes_after']==before, 'An input changed during execution')
        record.update(status='PASS_242_PACKAGE_VERIFICATION',
                      exact_machine_regenerated=True, input_bindings_unchanged=True,
                      working_states=242, transition_rows=484, guarded_cases=8390,
                      literal_transitions=6473406, blank_steps=407979,
                      all_transition_rows_covered=True)
    except BaseException as error:
        record.update(status='FAIL', error=repr(error))
        save()
        raise
    save()
    print(json.dumps({k:v for k,v in record.items()
                      if k not in ('commands','input_hashes_before','input_hashes_after')},indent=2))
    print(output/'verification.json')

if __name__=='__main__':
    main()
