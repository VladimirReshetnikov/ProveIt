#!/usr/bin/env python3
"""Recover source50 offline and replay the three new term-certificate suites.

All generation/execution occurs outside the checkout. Original source50 is
recovered by maintained reproduce_157.py --prepare-only; none of its manifests
or suites runs. This runner supplies no Lean build or binary-TM state count.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time

HOST = Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')
EXPERIMENT = Path('Computability/BusyBeaver/Research/ZFC/term-certificates')
SOURCES = ('term_paths.py', 'test_paths.py', 'term_circuits.py',
           'test_circuits.py', 'term_codec.py', 'test_codec.py')
DEPENDENCIES = ('code/symbolic254.py', 'code/canonical254.py',
                'code/term254.py', 'code/check_term254.py', 'data/spec254.json')


def identity(path: Path) -> dict:
    data = path.read_bytes()
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data).hexdigest()}


def standalone(run: Path, spec: Path, output: Path) -> None:
    """Fresh child checks the core using hosted spec, importing no producers."""
    sys.path.insert(0, str(run))
    import term_circuits as V
    import term_codec as B
    tables = V.load_templates(spec)
    example = json.loads((run / 'example-circuit-bundle.json').read_text())
    word = (run / 'example-bundle.bits').read_text()
    cert = B.decode(word, tables)
    assert cert == example['certificate']
    assert B.encode(cert, tables) == word
    assert V.verify_certificate(cert, tables, goal=example['trusted_control_goal'])
    assert not B.accepts(word, tables)
    prohibited = ('symbolic254', 'canonical254', 'term254', 'term_paths',
                  'test_paths', 'test_circuits', 'test_codec')
    assert not any(name in sys.modules for name in prohibited)
    assert Path(V.__file__).resolve() == (run / 'term_circuits.py').resolve()
    assert Path(B.__file__).resolve() == (run / 'term_codec.py').resolve()
    output.write_text(json.dumps({
        'status': 'PASS', 'word_bits': len(word), 'roundtrip_exact': True,
        'positive_bundle_control': True, 'same_word_rejected_at_fixedF': True,
        'numeric_or_producer_modules_imported': False,
        'trusted_hosted_spec': identity(spec),
        'scope': 'Clean-process stdlib-only verifier/codec finite control; no logical acceptance or TM state claim.'}, indent=2)+'\n')


def main() -> None:
    if not __debug__:
        raise SystemExit('Keep assertions enabled; do not use -O or PYTHONOPTIMIZE.')
    sys.dont_write_bytecode = True
    if len(sys.argv) > 1 and sys.argv[1] == '_standalone':
        if len(sys.argv) != 5:
            raise SystemExit('Expected run directory, hosted spec and output paths.')
        standalone(*(Path(p).resolve() for p in sys.argv[2:]))
        return
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, help='Repository checkout, when runner is outside it.')
    parser.add_argument('--output', type=Path, help='New or empty external scratch directory.')
    args = parser.parse_args()
    script = Path(__file__).resolve()
    repo = args.repo.resolve() if args.repo else next(
        (p for p in script.parents if (p / '.git').exists()), None)
    if repo is None:
        parser.error('Pass --repo when the runner is outside the checkout.')
    source = script.parent / 'term-certificates'
    missing = [name for name in SOURCES if not (source / name).is_file()]
    if missing:
        parser.error('Missing adjacent experiment sources: '+', '.join(missing))
    helper = repo / HOST / 'code/reproduce_157.py'
    spec = repo / HOST / 'data/50-terms-data-spec254.json'
    if not helper.is_file() or not spec.is_file():
        parser.error('The maintained source50 recovery helper and fixed hosted spec are required.')
    work = args.output.resolve() if args.output else Path(tempfile.mkdtemp(prefix='zfc-term-certificates-'))
    if work == repo or work.is_relative_to(repo) or (work.exists() and any(work.iterdir())):
        parser.error('Use a new or empty scratch directory outside the checkout.')
    work.mkdir(parents=True, exist_ok=True)
    record = {
        'status': 'RUNNING', 'python': sys.version, 'scratch': str(work),
        'repository_HEAD': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repo, text=True).strip(),
        'runner': identity(script), 'recovery_helper': identity(helper),
        'source50_arrival': '85633fd2f57b5dca16f87667699134d1b500ebc0',
        'source50_pin': 'fab89c5d26b81cd2ccab2ee5d213ff23725c7726',
        'fixed_hosted_spec': identity(spec),
        'experiment_sources': {name: identity(source / name) for name in SOURCES},
        'checks': [], 'Lean_built': False, 'Coq_built': False,
        'delivered_manifest_checks': False, 'delivered_suites_run': False,
        'assertions_enabled': True,
        'scope': 'Finite exact-C254 verifier/circuit/codec controls and fair-search specification; no actual binary TM, state price, consistency assertion or PA theorem.'}
    evidence = work / 'verification.json'
    def save():
        evidence.write_text(json.dumps(record, indent=2)+'\n')
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
    environment.pop('PYTHONOPTIMIZE', None)
    environment.pop('PYTHONPATH', None)
    def run(name, command, cwd):
        started = time.monotonic()
        log = work / (name+'.log')
        with log.open('w') as stream:
            result = subprocess.run(command, cwd=cwd, env=environment,
                                    stdout=stream, stderr=subprocess.STDOUT)
        elapsed = time.monotonic()-started
        record['checks'].append({'name':name,'command':command,'cwd':str(cwd),
                                 'returncode':result.returncode,'seconds':round(elapsed,3),'log':str(log)})
        save()
        print(f'{name}: exit {result.returncode}, {elapsed:.3f}s', flush=True)
        if result.returncode:
            record['status'] = 'FAIL'; save()
            raise SystemExit(f'{name} failed; inspect {log}.')
    save()
    recovered = work / 'recovered'
    run('source50-prepare-only', [sys.executable,'-B',str(helper),'--repo',str(repo),
                                '--output',str(recovered),'--prepare-only'], work)
    recovery = json.loads((recovered / 'verification.json').read_text())
    if recovery['status'] != 'PREPARED':
        raise RuntimeError('Source50 recovery did not finish in prepare-only mode.')
    package = Path(recovery['package'])
    if (package / 'data/spec254.json').read_bytes() != spec.read_bytes():
        raise RuntimeError('Recovered fixed specification differs from actual hosted data.')
    record['source50_recovery'] = recovery
    record['source50_test_dependencies'] = {name:identity(package / name) for name in DEPENDENCIES}
    run_dir = work / 'run'
    run_dir.mkdir()
    shutil.copytree(package, run_dir / 'source50')
    for name in SOURCES:
        shutil.copyfile(source / name, run_dir / name)
    for name, result_name in [('test_paths.py','results.json'),
                              ('test_circuits.py','circuit-results.json'),
                              ('test_codec.py','codec-results.json')]:
        run(name.removesuffix('.py'),[sys.executable,'-B',str(run_dir / name)],run_dir)
        result = json.loads((run_dir / result_name).read_text())
        if result['status'] != 'PASS':
            raise RuntimeError(name+' did not record PASS.')
        record[name.removesuffix('.py')] = result
        save()
    run('stdlib-hosted-spec',[sys.executable,'-B',str(script),'_standalone',str(run_dir),
                             str(spec),str(work / 'standalone.json')],run_dir)
    record['stdlib_hosted_spec'] = json.loads((work / 'standalone.json').read_text())
    if record['stdlib_hosted_spec']['status'] != 'PASS':
        raise RuntimeError('Independent-process core replay did not pass.')
    if not all((run_dir / name).read_bytes() == (source / name).read_bytes() for name in SOURCES):
        raise RuntimeError('Experiment code changed during replay.')
    if not all((run_dir / 'source50' / name).read_bytes() == (package / name).read_bytes()
               for name in DEPENDENCIES):
        raise RuntimeError('A recovered functional dependency changed during replay.')
    record['experiment_sources_unchanged'] = True
    record['recovered_functional_dependencies_unchanged'] = True
    record['fixed_spec_exact'] = True
    record['status'] = 'PASS'
    record['seconds_in_subprocesses'] = sum(c['seconds'] for c in record['checks'])
    save()
    print('Evidence:',evidence,flush=True)


if __name__ == '__main__':
    main()
