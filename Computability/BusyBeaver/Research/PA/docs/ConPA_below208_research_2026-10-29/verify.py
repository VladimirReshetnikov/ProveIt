#!/usr/bin/env python3
"""Offline audit of this research dossier; no nonhalting claim is tested.

Default: integrity, all snapshot comparisons, finite-model theorem certificate,
rejected-prefix witness, all279936 parameter choices, and finite baseline replay.
--full-runtime additionally rederives all5084 universal contracts for BOTH208
classes using the exact retained research-release engine.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import stat
import subprocess
import sys
import tempfile
import time
import zipfile

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent


def require(condition, message):
    if not condition:
        raise ValueError(message)


def check_manifest():
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    for name, expected in manifest['files'].items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Unsafe manifest path')
        path = ROOT/relative
        require(path.is_file() and not path.is_symlink(), 'Missing or linked payload: '+name)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == expected,
                'Payload hash mismatch: '+name)
    return len(manifest['files'])


def extract(archive, destination):
    destination.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(archive) as source:
        for entry in source.infolist():
            relative = Path(entry.filename)
            require(not relative.is_absolute() and '..' not in relative.parts,
                    'Unsafe archive member: '+entry.filename)
            require(not stat.S_ISLNK(entry.external_attr >> 16), 'Archive link rejected')
            require((destination/relative).resolve().is_relative_to(destination.resolve()),
                    'Archive path escape')
        source.extractall(destination)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--full-runtime', action='store_true')
    parser.add_argument('--output', type=Path, help='Receipt path outside the sealed release')
    args = parser.parse_args()
    require(not args.full_runtime or (__debug__ and not sys.flags.optimize),
            'Inherited full symbolic engines require Python without -O')
    if args.output:
        require(not args.output.resolve().is_relative_to(ROOT),
                'Write the receipt outside the sealed release')
    began = time.monotonic()
    files = check_manifest()
    checks = {}
    with tempfile.TemporaryDirectory(prefix='conpa-dossier-') as temporary:
        temp = Path(temporary)
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')
        def run(name, script, arguments=(), optimized=False):
            command = [sys.executable, '-B', '-E'] + (['-O'] if optimized else [])
            command += [str(script)] + [str(a) for a in arguments]
            result = subprocess.run(command, cwd=temp, env=environment, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            require(result.returncode == 0, name+' failed:\n'+result.stdout)
            print(name+': PASS', flush=True)
            return result.stdout

        compare_output = temp/'comparison.json'
        run('Independent snapshot comparison', ROOT/'code/compare_snapshots.py',
            ['--output', compare_output])
        checks['comparison'] = json.loads(compare_output.read_text())
        run('Optimized independent comparison', ROOT/'code/compare_snapshots.py',
            ['--output', temp/'comparison_optimized.json'], optimized=True)

        collision_text = run('Collision-only finite model', ROOT/'code/collision_only.py')
        checks['collision'] = json.loads(collision_text)
        require(checks['collision']['predicates_checked'] == 4
                and checks['collision']['full_true_cover_at_u'] is False,
                'Unexpected finite-model result')

        witness_output = temp/'prefix.json'
        run('Rejected-rotation regression witness', ROOT/'research/rejected_rotation/check_prefix.py',
            [ROOT/'baseline/snapshots/u209_joint/native.tm',
             ROOT/'research/rejected_rotation/rejected208.native.tm', '--output', witness_output])
        checks['rejected_prefix'] = json.loads(witness_output.read_text())

        permutation_output = temp/'permutations'
        run('Exhaustive279936-parameter census', ROOT/'research/axiom_permutations/exhaust.py',
            ['--output', permutation_output])
        checks['permutations'] = json.loads((permutation_output/'census.json').read_text())
        require(checks['permutations']['combinations'] == 279936
                and checks['permutations']['minimum_dag_nodes'] == 197
                and len(checks['permutations']['minimizers']) == 4,
                'Unexpected exhaustive-family result')

        contexts_receipt = temp/'source_context_dependencies.json'
        run('Source-context data and dependency audit', ROOT/'research/source_contexts/replay.py',
            ['--output', contexts_receipt])
        checks['source_context_dependencies'] = json.loads(contexts_receipt.read_text())
        local_output = temp/'local_relations'
        run('Local-relation input and completed-receipt audit', ROOT/'research/local_relations/run.py',
            ['--mode', 'verify', '--output', local_output])
        checks['local_relation_receipts'] = json.loads((local_output/'verification.json').read_text())

        entry_dir = temp/'entry'
        extract(ROOT/'baseline/U208_ConPA_Entry_Context_2026-10-29.zip', entry_dir)
        entry = entry_dir/'u208_conpa_entry_context_2026-10-29'
        run('Original Entry Context finite certificates', entry/'reproduce.py',
            ['--quick', '--output', temp/'entry_receipt.json'])
        checks['entry'] = json.loads((temp/'entry_receipt.json').read_text())

        research_dir = temp/'research'
        extract(ROOT/'baseline/u208_research_2026-10-29.zip', research_dir)
        upstream = research_dir/'u208_research_2026-10-29'
        upstream_args = ['--output', temp/'research_receipt.json']
        if args.full_runtime:
            print('Replaying both5084-contract universal runtimes; allow several minutes.', flush=True)
            upstream_args.append('--full')
        run('Original research-release '+('full runtimes' if args.full_runtime else 'finite certificates'),
            upstream/'verify.py', upstream_args)
        checks['research_release'] = json.loads((temp/'research_receipt.json').read_text())
        if not args.full_runtime:
            run('Optimized original research finite checks', upstream/'verify.py',
                ['--output', temp/'research_optimized.json'], optimized=True)

    receipt = {'status': 'DOSSIER_FULL_RUNTIME_REPLAY_PASS' if args.full_runtime else 'DOSSIER_FINITE_REPLAY_PASS',
               'manifest_files': files, 'checks': checks,
               'full_runtime_requested': args.full_runtime,
               'long_discovery_searches': 'Not rerun by this command; see research/two_row and research notes.',
               'new_207_state_construction': False,
               'scope': 'Exact comparisons and ordinary mathematical certificates; no new kernel-checked PA endpoint.',
               'seconds': time.monotonic()-began}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(receipt, indent=2)+'\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'checks'}, indent=2))


if __name__ == '__main__':
    main()
