#!/usr/bin/env python3
"""Bounded replay over the pinned V-bound overlay; no parent rebuild."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess

if not __debug__:
    raise RuntimeError('replay requires Python assertions enabled')

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'FreeJDenominator.lean'
PARENT_DIR = HERE.parent / 'free-j-graph-vbound-prototype'
PARENT_REPLAY = PARENT_DIR / 'replay.py'
PARENT_RECEIPT = PARENT_DIR / 'replay-receipt.json'
PARENT_OUTPUT = Path('/tmp/ipra-ordinary12-freej-vbound-replay-01')
BASE = PARENT_OUTPUT / 'lib'
SOURCE_HASH = '898b9fa159ba784cc32b71e639a159d785d14e67096aee18a8df07740e23b8a3'
PARENT_REPLAY_HASH = 'aa5f7535f902f3fd551f8be81a7fea4a321d6213c19f0decdf07eb89354f001c'
PARENT_RECEIPT_HASH = '31e4f1f541b437b28d37b55e03ea6194d27bf4c4c4009ed3f1bbffefdc453897'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--receipt', required=True, type=Path)
    args = ap.parse_args()
    out, receipt = args.output.absolute(), args.receipt.absolute()
    if out.exists() or out.is_symlink() or receipt.exists() or receipt.is_symlink():
        raise ValueError('refusing overwrite')
    if (digest(SOURCE), digest(PARENT_REPLAY), digest(PARENT_RECEIPT)) != (
        SOURCE_HASH, PARENT_REPLAY_HASH, PARENT_RECEIPT_HASH):
        raise ValueError('source or parent drift')
    spec = importlib.util.spec_from_file_location('graph_vbound_parent', PARENT_REPLAY)
    parent = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    meta = json.loads(PARENT_RECEIPT.read_text())
    seed_src = PARENT_OUTPUT / 'FreeJGraphVBound.olean'
    if meta.get('status') != 'PASS_BOUNDED_FREEJ_GRAPH_V_BOUND' or digest(seed_src) != meta['object_sha256']:
        raise ValueError('V-bound parent seed drift')
    if digest(BASE / 'DiophantineConsistency/FreeJEarlySize.olean') != digest(parent.PARENT/'FreeJEarlySize.olean'):
        raise ValueError('V-bound inherited seed drift')
    before = parent.parent_check()
    out.mkdir(parents=True)
    lib = out / 'lib'
    parent.overlay(BASE, lib)
    seed = lib / 'DiophantineConsistency/FreeJGraphVBound.olean'
    if seed.exists() or seed.is_symlink():
        raise ValueError('unexpected earlier graph-bound seed')
    shutil.copyfile(seed_src, seed)
    srcroot = out / 'src'
    src = srcroot / 'DiophantineConsistency/FreeJDenominator.lean'
    src.parent.mkdir(parents=True)
    shutil.copyfile(SOURCE, src)
    obj = out / 'FreeJDenominator.olean'
    env = os.environ.copy()
    for name in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(name, None)
    env['LEAN_PATH'] = str(lib) + ':' + str(parent.PACKAGE)
    cmd = [str(parent.LEAN), '-M3000', '-j1', '-DElab.async=false', '--root='+str(srcroot), str(src), '-o', str(obj)]
    proc = subprocess.run(cmd, env=env, text=True, capture_output=True, timeout=120)
    output = proc.stdout+proc.stderr
    if proc.returncode != 0 or 'sorryAx' in output or 'warning:' in output or output.count('depends on axioms:') != 7:
        raise ValueError(('Lean failure', proc.returncode, output))
    deps = subprocess.run([str(parent.LEAN), '--deps', str(src)], env=env, text=True, capture_output=True, timeout=30)
    if deps.returncode or set(deps.stdout.splitlines()) != {str(parent.PACKAGE/'Init.olean'), str(seed)}:
        raise ValueError(('unexpected direct dependencies', deps.returncode, deps.stdout, deps.stderr))
    if before != parent.parent_check() or digest(seed) != meta['object_sha256'] or digest(seed_src) != meta['object_sha256'] or digest(src) != SOURCE_HASH or digest(SOURCE) != SOURCE_HASH or digest(PARENT_RECEIPT) != PARENT_RECEIPT_HASH or digest(PARENT_REPLAY) != PARENT_REPLAY_HASH:
        raise ValueError('input changed during replay')
    data = {'status':'PASS_BOUNDED_FREEJ_DENOMINATOR', 'lean_exit_code':proc.returncode,
            'lean_command':cmd, 'lean_stdout':proc.stdout, 'lean_stderr':proc.stderr,
            'object_sha256':digest(obj), 'deps_exit_code':deps.returncode, 'deps_stdout':deps.stdout,
            'parent_vbound_receipt_sha256':PARENT_RECEIPT_HASH, 'parent_vbound_object_sha256':meta['object_sha256'],
            'checked_earlier_parent_inputs':before,
            'scope':'Single-author historical model overlay; reuses the V-bound historical overlay and package. Not a fresh full-source or package-transitive audit, compact44 calibration, or object-level iPRA proof.'}
    with receipt.open('x') as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write('\n')
    print('PASS_BOUNDED_FREEJ_DENOMINATOR', digest(receipt))

if __name__ == '__main__':
    main()
