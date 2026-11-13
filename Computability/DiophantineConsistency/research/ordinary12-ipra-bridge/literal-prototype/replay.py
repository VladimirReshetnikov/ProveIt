#!/usr/bin/env python3
"""Replay the exact ordinary12 literal/factor identities on a fresh overlay."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

if not __debug__:
    raise RuntimeError('replay guards require Python assertions enabled')
HERE = Path(__file__).resolve().parent
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
SOURCE = HERE / 'Ordinary12Literal.lean'
SOURCE_SHA = '23a22eebc33d262e1b4c134c6072e808c002aac31a627def951bc753d3e96709'
BASE_REPLAY = HERE.parent / 'model-prototype/replay.py'

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.absolute()
    if output.exists() or output.is_symlink() or args.receipt.exists() or args.receipt.is_symlink():
        raise ValueError('refusing to overwrite output or receipt')
    if H(SOURCE) != SOURCE_SHA: raise ValueError('literal source drift')
    input_hashes = {str(p): H(p) for p in (SOURCE, HERE/'check_literal.py', BASE_REPLAY, Path(__file__))}
    check = subprocess.run([sys.executable, str(HERE/'check_literal.py')], capture_output=True, text=True)
    if check.returncode: raise ValueError(('literal graph check failed', check.stdout, check.stderr))
    output.mkdir(parents=True)
    base = output/'base'; base_receipt = output/'base-receipt.json'
    inner = subprocess.run([sys.executable, str(BASE_REPLAY), '--output', str(base), '--receipt', str(base_receipt)],
                           capture_output=True, text=True)
    if inner.returncode: raise ValueError(('historical overlay replay failed', inner.stdout, inner.stderr))
    prior = json.loads(base_receipt.read_text())
    if prior['status'] != 'PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE': raise ValueError('wrong seed receipt')
    root = output/'literal/src'; src = root/'DiophantineConsistency/Ordinary12Literal.lean'
    src.parent.mkdir(parents=True); shutil.copyfile(SOURCE, src)
    obj = output/'literal/Ordinary12Literal.olean'
    env = os.environ.copy()
    for name in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(name, None)
    env['LEAN_PATH'] = str(base/'lib') + ':' + str(PACKAGE)
    command = [str(LEAN), '-M8000', '-j1', '-DElab.async=false', f'--root={root}', str(src), '-o', str(obj)]
    process = subprocess.run(command, env=env, capture_output=True, text=True)
    combined = process.stdout + process.stderr
    if process.returncode or 'sorryAx' in combined or 'warning:' in combined or combined.count('depends on axioms:') != 3:
        raise ValueError(('literal compilation failed', process.stdout, process.stderr))
    deps = subprocess.run([str(LEAN), '--deps', str(src)], env=env, capture_output=True, text=True)
    expected = {str(PACKAGE/'Init.olean'), str(base/'lib/DiophantineConsistency/ArithmeticAdaptiveFactorMagnitude2011.olean')}
    if deps.returncode or set(deps.stdout.splitlines()) != expected:
        raise ValueError(('unexpected direct imports', deps.stdout, deps.stderr))
    for link, metadata in prior['seed_links'].items():
        path = Path(link); target = Path(metadata['source'])
        if not path.is_symlink() or path.resolve() != target or H(target) != metadata['sha256']:
            raise ValueError(('historical seed drift', link))
    for name in prior['absent_parent_paths']:
        path = Path(name)
        if path.exists() or path.is_symlink(): raise ValueError(('new parent companion', name))
    if {p: H(Path(p)) for p in input_hashes} != input_hashes: raise ValueError('input drift')
    result = {'status': 'PASS_BOUNDED_ORDINARY12_LITERAL_IDENTITY', 'graph_check_exit_code': check.returncode,
              'graph_check_stdout': check.stdout, 'base_replay_exit_code': inner.returncode,
              'base_replay_stdout': inner.stdout, 'base_receipt_sha256': H(base_receipt), 'base_receipt': prior,
              'lean_exit_code': process.returncode, 'lean_stdout': process.stdout, 'lean_stderr': process.stderr,
              'lean_command': command, 'object_sha256': H(obj), 'direct_deps_exit_code': deps.returncode,
              'direct_deps_stdout': deps.stdout, 'inputs_sha256': input_hashes,
              'scope': 'Historical single-author isolated literal identity only; no concrete factor exclusions, full guarded pair, compact44 calibration, rank recovery or iPRA proof.'}
    with args.receipt.open('x') as f: json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print('PASS_BOUNDED_ORDINARY12_LITERAL_IDENTITY', H(args.receipt))

if __name__ == '__main__':
    main()
