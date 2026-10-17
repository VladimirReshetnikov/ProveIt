#!/usr/bin/env python3
"""Replay the supplied substantive checks in an isolated temporary package.

No long state search is repeated. Original records and sources are unchanged.
Only Python's standard library is needed; assertions must remain enabled.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def main():
    if not __debug__:
        raise SystemExit('Run without -O or PYTHONOPTIMIZE')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    base = Path(__file__).resolve().parents[1]
    begun = time.monotonic()
    checks = []
    with tempfile.TemporaryDirectory(prefix='c254-package-replay-') as tmp:
        work = Path(tmp)
        for name in ('code', 'data', 'reference', 'machine_experiments'):
            shutil.copytree(base/name, work/name,
                            ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))

        def run(name, argv, stdout_json=None):
            started = time.monotonic()
            proc = subprocess.run([sys.executable, '-B', *argv], cwd=work,
                                  text=True, capture_output=True)
            if proc.returncode:
                raise RuntimeError(name + '\n' + proc.stdout + '\n' + proc.stderr)
            if stdout_json:
                parsed = json.loads(proc.stdout)
                (work/stdout_json).write_text(json.dumps(parsed, indent=2)+'\n')
            checks.append({'name':name, 'status':'PASS',
                           'seconds':round(time.monotonic()-started, 3)})
            print('PASS:', name, flush=True)

        source = ('reference/proveit/Computability/BusyBeaver/Lean/'
                  'BusyBeaver/ZFC/Code254.lean')
        run('literal source extraction', ['code/extract_specs.py', source,
                                         'data/reextracted_spec254.json'])
        assert json.loads((work/'data/reextracted_spec254.json').read_text()) == \
            json.loads((work/'data/spec254.json').read_text())
        run('sparse and canonical comparison', ['code/reproduce.py','--output','data'])
        run('independent quotation and fuel audit',
            ['code/check_proof_code_size.py'], 'data/proof_code_size_results.json')
        run('independent canonical verifier audit', ['code/audit_canonical.py'])
        run('fixed-template metrics', ['code/schema_metrics.py','--check'])
        run('constructor-only verifier audit', ['code/check_term254.py'])
        # All deterministic saved results must match their fresh counterparts.
        for name in ('proof_code_size_results.json','canonical_audit_results.json',
                     'schema_metrics.json','term_certificate_results.json',
                     'example_certificate.json','example_mp_certificate.json',
                     'example_term_bundle_control.json'):
            assert json.loads((work/'data'/name).read_text()) == \
                   json.loads((base/'data'/name).read_text()), name
        for file in ('sparse_certificate_results.json',):
            fresh = json.loads((work/'data'/file).read_text())
            saved = json.loads((base/'data'/file).read_text())
            fresh.pop('seconds'); saved.pop('seconds')
            assert fresh == saved, file

        table = ('reference/proveit/Computability/BusyBeaver/Research/ZFC/'
                 'candidate-permutation252/zfc_permutation252_old.tm')
        for degree in (1,2):
            run('degree-%d compressed partition replay' % degree,
                ['machine_experiments/replay_entry_partition.py', '--result',
                 'machine_experiments/entry_degree%d.json' % degree,
                 '--table', table, '--output', 'partition%d.json' % degree])
        run('literal continuation and residual replay',
            ['machine_experiments/continuation_obstruction.py', '--repo',
             'reference/proveit', '--output', 'continuation_replayed.json'])
        assert json.loads((work/'continuation_replayed.json').read_text()) == \
            json.loads((base/'machine_experiments/continuation_obstruction.json').read_text())

        # Recheck the baseline contracts and literal boot without a fresh search.
        path = work/'machine_experiments/entry_resynthesis.py'
        spec = importlib.util.spec_from_file_location('replay_entry_driver',path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        h = module.Harness(work/'reference/proveit',1000)
        assert len(h.cases) == 8391
        checks.append({'name':'baseline 8391 cases and 82552-step exact boot',
                       'status':'PASS'})
        print('PASS: baseline 8391 cases and 82552-step exact boot',flush=True)

        # Preserve and explain the observed degree-one transport difference.
        norm = json.loads((base/'machine_experiments/transport_normalization.json').read_text())
        for name,row in norm['files'].items():
            b=(work/'reference/proveit'/name).read_bytes()
            assert hashlib.sha256(b).hexdigest()==row['canonical_reference_sha256']
            assert hashlib.sha256(b+b'\n').hexdigest()==row['degree1_observed_sha256']
        checks.append({'name':'degree-one transport provenance','status':'PASS'})

    result = {'status':'PASS','scope':'Finite substantive replays; no long search, kernel rebuild, new machine or consistency assertion.',
              'checks':checks,'seconds':round(time.monotonic()-begun,3),
              'python':sys.version.split()[0]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print('All %d checks passed; report: %s' % (len(checks), args.output))


if __name__ == '__main__':
    main()
