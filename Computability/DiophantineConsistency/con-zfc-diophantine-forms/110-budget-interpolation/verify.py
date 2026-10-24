#!/usr/bin/env python3
"""Portable, offline, isolated release replay. Not a consistency proof.

Run normally: this driver explicitly runs every new checker in normal and -O
Python, plus the declared prior-release replays. Python >=3.10 and SymPy are
required. No network access, package installation, or external data are used.
"""
from pathlib import Path
import argparse
import concurrent.futures
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent


def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def authenticate(root):
    root = root.resolve()
    manifest = json.loads((root/'SHA256SUMS.json').read_text())
    require(isinstance(manifest, dict) and bool(manifest), 'Empty release manifest')
    for name, expected in manifest.items():
        relative = Path(name)
        require(not relative.is_absolute() and '..' not in relative.parts,
                'Unsafe manifest path: '+name)
        path = root/relative
        require(not path.is_symlink() and path.resolve().is_relative_to(root),
                'Unsafe file: '+name)
        require(path.is_file() and digest(path) == expected, 'Manifest mismatch: '+name)
    actual = set()
    for path in root.rglob('*'):
        require(not path.is_symlink(), 'Symlink in release: '+str(path.relative_to(root)))
        if path.is_file() and '__pycache__' not in path.parts and path.suffix != '.pyc':
            actual.add(path.relative_to(root).as_posix())
    require(actual == set(manifest)|{'SHA256SUMS.json'},
            'Unsealed or missing files: '+str(sorted(actual^(set(manifest)|{'SHA256SUMS.json'}))))
    return manifest


def corruption_controls(root):
    controls = []
    with tempfile.TemporaryDirectory(prefix='wave13-corruption-') as td:
        clone = Path(td)/'release'
        shutil.copytree(root, clone, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
        for name in ('guard/budget12_tau_centered.json', 'guard/coefficients/BINDING.json',
                     'guard/coefficients/beta.bin.gz', 'eleven/PROOF.md'):
            p = clone/name
            original = p.read_bytes()
            p.write_bytes(original+b'\n')
            try:
                authenticate(clone)
            except RuntimeError:
                controls.append({'target':name, 'mutation':'append one newline', 'rejected':True})
            else:
                raise RuntimeError('Corruption escaped manifest: '+name)
            p.write_bytes(original)
        p = clone/'positive/ten_centered/generated/p10_positive.json'
        original = p.read_bytes()
        p.unlink()
        try:
            authenticate(clone)
        except RuntimeError:
            controls.append({'target':str(p.relative_to(clone)), 'mutation':'remove file', 'rejected':True})
        else:
            raise RuntimeError('Missing artifact escaped manifest')
        p.write_bytes(original)
        p = clone/'UNSEALED_TEST.txt'
        p.write_text('deliberate negative control\n')
        try:
            authenticate(clone)
        except RuntimeError:
            controls.append({'target':p.name, 'mutation':'unsealed extra file', 'rejected':True})
        else:
            raise RuntimeError('Unsealed file escaped manifest')
        p.unlink()
        authenticate(clone)
    return controls


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest-only', action='store_true')
    parser.add_argument('--output', type=Path, help='Optional JSON receipt outside this immutable release')
    parser.add_argument('--jobs', type=int, default=3, help='Independent isolated replay groups in parallel')
    args = parser.parse_args()
    require(sys.version_info >= (3, 10), 'Python >=3.10 required')
    require(not sys.flags.optimize, 'Run this master normally; it explicitly includes all optimized stages')
    require(args.jobs >= 1, '--jobs must be positive')
    output = args.output.resolve() if args.output else None
    require(output is None or not output.is_relative_to(ROOT), 'Receipt must be outside the immutable release')
    before = authenticate(ROOT)
    if args.manifest_only:
        print(json.dumps({'status':'PASS', 'sealed_files':len(before)}))
        return
    import sympy
    plan = json.loads((ROOT/'REPLAY_PLAN.json').read_text())
    started = time.monotonic()
    environment = dict(os.environ, PYTHONDONTWRITEBYTECODE='1', PYTHONHASHSEED='0')
    environment.pop('PYTHONOPTIMIZE', None)
    environment.pop('PYTHONPATH', None)

    def replay(group):
        records = []
        tick_group = time.monotonic()
        with tempfile.TemporaryDirectory(prefix='wave13-'+group['name']+'-') as td:
            work = Path(td)/'release'
            shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns('__pycache__', '*.pyc'))
            for stage in group['commands']:
                argv = [value.replace('{TEMP}', td) for value in stage['argv']]
                command = [sys.executable, '-B', *argv]
                tick = time.monotonic()
                run = subprocess.run(command, cwd=work, env=environment,
                                     stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                     timeout=1800)
                if run.returncode:
                    print(run.stdout.decode(errors='replace'))
                    print(run.stderr.decode(errors='replace'), file=sys.stderr)
                require(run.returncode == 0, 'Replay failed: '+' '.join(argv))
                compared = stage.get('byte_identical', [])
                for name in compared:
                    require((work/name).read_bytes() == (ROOT/name).read_bytes(),
                            'Nonidentical rebuilt artifact: '+name)
                records.append({'stage':stage['label'], 'argv':stage['argv'], 'status':'PASS',
                                'seconds':round(time.monotonic()-tick, 3),
                                'byte_identical_rebuilt_files':compared,
                                'stdout_sha256':hashlib.sha256(run.stdout).hexdigest(),
                                'stderr_sha256':hashlib.sha256(run.stderr).hexdigest()})
                print('PASS '+group['name']+' / '+stage['label'], flush=True)
            receipts = {}
            for name in group.get('receipts', []):
                source = Path(name.replace('{TEMP}', td))
                if not source.is_absolute():
                    source = work/source
                require(source.is_file(), 'Missing replay receipt: '+name)
                receipts[name] = json.loads(source.read_text())
        return {'name':group['name'], 'status':'PASS', 'commands':records,
                'receipts':receipts, 'seconds':round(time.monotonic()-tick_group, 3)}

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as executor:
        results = list(executor.map(replay, plan['groups']))
    controls = corruption_controls(ROOT)
    require(authenticate(ROOT) == before, 'Immutable release changed during replay')
    result = {'status':'PASS', 'python':sys.version, 'sympy':sympy.__version__,
              'sealed_files':len(before), 'groups':results,
              'command_count':sum(len(g['commands']) for g in results),
              'manifest_corruption_controls':controls, 'source_release_unchanged':True,
              'elapsed_seconds':round(time.monotonic()-started, 3),
              'scope':'Finite exact identities, literal DAGs, actual coefficients, exact degrees, source authentication, deterministic rebuilds and corruption controls. Ordinary unbounded proofs and inherited native/compiler/Pell/refutation calibration are separate. Power/binomial graph interfaces are not ordinary-polynomial records.'}
    if output:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
