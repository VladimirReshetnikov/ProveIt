#!/usr/bin/env python3
"""Offline reconstruction and verification of the K227 research package.

Quick mode audits stored complete runtime proofs; --full rederives the final
K227 universal runtime as well. Neither mode invokes Rocq or claims a kernel
endpoint. All fresh outputs go to a new directory outside the package.
"""
from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT/'verification'))
from verify_runtime import parse_table, require
import verify_state_fold as fold


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def save(p, data):
    p.write_text(json.dumps(data, indent=2)+'\n')


def renumbering(n):
    old = parse_table(ROOT/'machines'/f'k{n}_inherited.tm')
    data = json.loads((ROOT/'machines'/f'k{n}_renumbering.json').read_text())
    ren = {int(q): z for q, z in data['inherited_to_canonical'].items()}
    old_states = {q for q, b in old}
    require(set(ren) == old_states | {254}, 'Incomplete renumbering domain')
    require(set(ren.values()) == set(range(n+1)) and len(ren) == n+1,
            'Renumbering is not bijective')
    require(ren[95] == 0 and ren[254] == n and data['dispatcher'] == ren[96],
            'Wrong canonical interfaces')
    canonical, starts = {}, []
    for line in (ROOT/'machines'/f'k{n}.tm').read_text().splitlines():
        if line.startswith('#! start '):
            starts.append(int(line.split()[-1]))
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            require((q, b) not in canonical and d in ('L', 'R'), 'Canonical row')
            canonical[q, b] = w, 1 if d == 'R' else -1, z
    expected = {(ren[q], b): (w, d, ren[z]) for (q, b), (w, d, z) in old.items()}
    require(canonical == expected and starts == [0], 'Literal renumbering differs')
    require(set(canonical) == {(q, b) for q in range(n) for b in (0, 1)}, 'Wrong census')
    return dict(states=n, status='PASS_EXACT_STATE_BIJECTION',
                inherited_sha256=sha(ROOT/'machines'/f'k{n}_inherited.tm'),
                canonical_sha256=sha(ROOT/'machines'/f'k{n}.tm'),
                start=0, dispatcher=ren[96], halt=n, rows=2*n)


def main():
    require(__debug__ and not sys.flags.optimize, 'Run with assertions enabled')
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir', type=Path, required=True)
    p.add_argument('--full', action='store_true')
    a = p.parse_args()
    out = a.output_dir.resolve()
    require(out != ROOT and ROOT not in out.parents, 'Choose an output outside the package')
    require(not out.exists(), 'Output directory must be new')
    out.mkdir(parents=True)
    began = time.monotonic()
    result = dict(status='IN_PROGRESS', full_runtime_requested=a.full, steps=[])
    resultp = out/'replay.json'

    def record(name, details):
        result['steps'].append(dict(name=name, **details))
        result['seconds'] = time.monotonic()-began
        save(resultp, result)

    def run(name, script, *args):
        log = out/(name+'.log')
        command = [sys.executable, '-B', str(script), *map(str, args)]
        env = os.environ.copy()
        env.pop('PYTHONOPTIMIZE', None)
        env['PYTHONDONTWRITEBYTECODE'] = '1'
        print(name, flush=True)
        with log.open('w') as stream:
            proc = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT,
                                  env=env, cwd=out, timeout=900)
        require(proc.returncode == 0, f'{name} failed; see {log}')
        record(name, dict(status='PASS', log=log.name))

    try:
        manifest = json.loads((ROOT/'manifest.json').read_text())
        for name, item in manifest['files'].items():
            path = ROOT/name
            require(not Path(name).is_absolute() and '..' not in Path(name).parts, 'Unsafe manifest path')
            require(path.is_file() and path.stat().st_size == item['bytes']
                    and sha(path) == item['sha256'], 'Manifest mismatch: '+name)
        record('manifest', dict(status='PASS', files=len(manifest['files'])))
        built = out/'rebuilt'
        run('construct', ROOT/'build.py', '--output-dir', built)
        for pth in built.glob('*.tm'):
            require(pth.read_bytes() == (ROOT/'machines'/pth.name).read_bytes(),
                    'Reconstructed table differs: '+pth.name)
        for pth in built.glob('*_sites*'):
            require(pth.read_bytes() == (ROOT/'source'/pth.name).read_bytes(),
                    'Reconstructed source differs: '+pth.name)
        maps = [renumbering(n) for n in (229, 228, 227)]
        save(out/'renumbering.json', maps)
        record('canonical_bijections', dict(status='PASS', states=[229, 228, 227]))
        v = ROOT/'verification'
        ref = ROOT/'reference/k230-rocq'
        run('literal_bindings', v/'check_k230_literal_bindings.py',
            '--repo', ref, '--out', out/'literal_bindings.json')
        run('upstream_source_audit', v/'audit_k230_sources.py',
            '--repo', ref, '--out', out/'upstream_source_audit.json')
        run('uniform_loop_induction', v/'check_loop_identity.py',
            '--output', out/'uniform_loop_induction.json')
        basis = parse_table(ROOT/'machines/k230_posttest_inherited.tm')
        k229 = parse_table(ROOT/'machines/k229_inherited.tm')
        f = fold.prove(basis, k229, 95, 95, 72, 90, 0, None, 5, 65, 20000)
        require(f['status'] == 'PASS_ALL_TAPE_POSITIVE_BLOCK_SIMULATION', 'K229 fold not proved')
        save(out/'fold229.json', f)
        record('fold229', dict(status='PASS', old_rows=460))
        run('guarded_fold228', v/'check_k228_local.py',
            '--old', ROOT/'machines/k229_inherited.tm',
            '--new', ROOT/'machines/k228_inherited.tm', '--output', out/'guarded_fold228.json')
        run('source_graph227', v/'audit_source_graph.py',
            ROOT/'source/k228_sites_logical.json', ROOT/'source/k227_sites_logical.json',
            '--output', out/'source_graph227.json')
        run('split_fold227', v/'verify_split_fold.py',
            '--basis', ROOT/'machines/k228_rotated_inherited.tm',
            '--candidate', ROOT/'machines/k227_inherited.tm', '--output', out/'split_fold227.json')
        run('independent_build227', v/'build_k227_independent.py',
            '--baseline-table', ROOT/'machines/k228_inherited.tm',
            '--baseline-source', ROOT/'source/k228_sites_logical.json',
            '--output-dir', out/'independent227')
        require((out/'independent227/k227_old.tm').read_bytes() ==
                (ROOT/'machines/k227_inherited.tm').read_bytes(), 'Independent table builder differs')
        require((out/'independent227/sites_logical.json').read_bytes() ==
                (ROOT/'source/k227_sites_logical.json').read_bytes(), 'Independent source builder differs')
        for n in (228, 227):
            run(f'bootstrap{n}', v/'verify_bootstrap.py', '--table',
                ROOT/'machines'/f'k{n}_inherited.tm', '--steps', 409835,
                '--output', out/f'bootstrap{n}.json')
        run('stored_runtime_audit', v/'audit_receipts.py',
            '--root', ROOT, '--output', out/'stored_runtime_audit.json')
        run('adversarial', v/'adversarial_tests.py',
            '--driver', v/'verify_runtime.py', '--bootstrap-driver', v/'verify_bootstrap.py',
            '--engine-dir', v/'engine', '--table', ROOT/'machines/k227_inherited.tm',
            '--sites', ROOT/'source/k227_sites_logical.json', '--output-dir', out/'adversarial')
        run('alternative_source_only', ROOT/'alternatives/canonical_v/build.py',
            '--out', out/'canonical_v')
        require((out/'canonical_v/sites_logical.json').read_bytes() ==
                (ROOT/'alternatives/canonical_v/sites_logical.json').read_bytes(),
                'Alternative source reproduction differs')
        if a.full:
            run('fresh_universal_runtime227', v/'verify_runtime.py',
                '--engine-dir', v/'engine', '--table', ROOT/'machines/k227_inherited.tm',
                '--sites', ROOT/'source/k227_sites_logical.json', '--states', 227,
                '--leaves', 5121, '--cases', 6656, '--output', out/'runtime227.json')
            fresh = json.loads((out/'runtime227.json').read_text())
            stored = json.loads((ROOT/'evidence/runtime227.json').read_text())
            require(fresh['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
                    and fresh['cases_sha256'] == stored['cases_sha256'],
                    'Fresh universal proof does not reproduce the stored case data')
        result.update(status='PASS_FULL_REPLAY' if a.full else 'PASS_QUICK_REPLAY',
                      ordinary_mathematical_verification=True, rocq_rebuild=False,
                      fresh_universal_runtime=a.full,
                      stored_runtime_audit_only=not a.full,
                      seconds=time.monotonic()-began)
        save(resultp, result)
        print(json.dumps({k: v for k, v in result.items() if k != 'steps'}, indent=2), flush=True)
    except Exception as exc:
        result.update(status='FAILED', error=repr(exc), seconds=time.monotonic()-began)
        save(resultp, result)
        raise


if __name__ == '__main__':
    main()

