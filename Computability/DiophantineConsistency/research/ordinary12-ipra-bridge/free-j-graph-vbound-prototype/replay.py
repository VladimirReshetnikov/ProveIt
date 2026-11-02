#!/usr/bin/env python3
"""Compile the graph V bound against its checked historical model parent.

This reuses, rather than rebuilds, the historical package and parent closure.
It is not a current-source, package-transitive or object-level iPRA replay.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

if not __debug__:
    raise RuntimeError('replay requires Python assertions enabled')

HERE = Path(__file__).resolve().parent
SOURCE = HERE / 'FreeJGraphVBound.lean'
PARENT_RECEIPT = HERE.parent / 'free-j-early-size-prototype/replay-receipt.json'
PARENT = Path('/tmp/ipra-ordinary12-early-size-replay-01')
BASE = PARENT / 'comparison/early/pell/rank/rank/rank/rank/freej/concrete/composed/base/lib'
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
SOURCE_HASH = '1737e236991405073c78079c4b529ca67296ec7f72dd74006592ad98b7354795'
RECEIPT_HASH = 'a8d63f37e23973b148db16b6eedc3c6a88b0d15ef248d6db14608d142867b865'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def parent_check():
    if digest(SOURCE) != SOURCE_HASH or digest(PARENT_RECEIPT) != RECEIPT_HASH:
        raise ValueError('source or historical parent receipt drift')
    d = json.loads(PARENT_RECEIPT.read_text())
    if d.get('status') != 'PASS_BOUNDED_FREEJ_EARLY_SIZE':
        raise ValueError('unexpected parent status')
    checked = {str(SOURCE): digest(SOURCE), str(PARENT_RECEIPT): digest(PARENT_RECEIPT),
               str(LEAN): digest(LEAN)}
    while True:
        expected = d.get('object_sha256')
        cmd = d.get('lean_command')
        if expected and cmd:
            obj = Path(cmd[-1])
            if digest(obj) != expected:
                raise ValueError(('parent object drift', str(obj)))
            checked[str(obj)] = expected
            if obj.name != 'FreeJEarlySize.olean':
                bound = BASE / 'DiophantineConsistency' / obj.name
                if digest(bound) != expected:
                    raise ValueError(('parent overlay object drift', str(bound)))
                checked[str(bound)] = expected
        for name, expected in d.get('generated_objects', {}).items():
            obj = BASE / 'DiophantineConsistency' / (name + '.olean')
            if digest(obj) != expected:
                raise ValueError(('generated parent object drift', str(obj)))
            checked[str(obj)] = expected
        for link, meta in d.get('seed_links', {}).items():
            link, target = Path(link), Path(meta['source'])
            if not link.is_symlink() or link.resolve() != target or digest(target) != meta['sha256']:
                raise ValueError(('seed link drift', str(link)))
            checked[str(target)] = meta['sha256']
        for path, expected in d.get('pinned_inputs', {}).items():
            if digest(path) != expected:
                raise ValueError(('pinned parent drift', path))
            checked[path] = expected
        for path in d.get('absent_parent_paths', []):
            path = Path(path)
            if path.exists() or path.is_symlink():
                raise ValueError(('parent companion appeared', str(path)))
        if 'inner_receipt' not in d:
            break
        d = d['inner_receipt']
    return checked

def overlay(base, destination):
    for root, dirs, files in os.walk(base, followlinks=False):
        root = Path(root)
        out = destination / root.relative_to(base)
        out.mkdir(parents=True, exist_ok=True)
        for name in list(dirs):
            src = root / name
            if src.is_symlink():
                (out / name).symlink_to(src)
                dirs.remove(name)
        for name in files:
            (out / name).symlink_to(root / name)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', required=True, type=Path)
    ap.add_argument('--receipt', required=True, type=Path)
    args = ap.parse_args()
    out, receipt = args.output.absolute(), args.receipt.absolute()
    if out.exists() or out.is_symlink() or receipt.exists() or receipt.is_symlink():
        raise ValueError('refusing overwrite')
    before = parent_check()
    out.mkdir(parents=True)
    lib = out / 'lib'
    overlay(BASE, lib)
    seed = lib / 'DiophantineConsistency/FreeJEarlySize.olean'
    if seed.exists() or seed.is_symlink():
        raise ValueError('unexpected earlier seed')
    shutil.copyfile(PARENT / 'FreeJEarlySize.olean', seed)
    srcroot = out / 'src'
    src = srcroot / 'DiophantineConsistency/FreeJGraphVBound.lean'
    src.parent.mkdir(parents=True)
    shutil.copyfile(SOURCE, src)
    obj = out / 'FreeJGraphVBound.olean'
    env = os.environ.copy()
    for name in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(name, None)
    env['LEAN_PATH'] = str(lib) + ':' + str(PACKAGE)
    cmd = [str(LEAN), '-M3000', '-j1', '-DElab.async=false', '--root='+str(srcroot), str(src), '-o', str(obj)]
    proc = subprocess.run(cmd, env=env, text=True, capture_output=True, timeout=120)
    output = proc.stdout + proc.stderr
    expected_reports = 5
    if proc.returncode != 0 or 'sorryAx' in output or 'warning:' in output or output.count('depends on axioms:') != expected_reports:
        raise ValueError(('Lean failure', proc.returncode, output))
    deps = subprocess.run([str(LEAN), '--deps', str(src)], env=env, text=True, capture_output=True, timeout=30)
    if deps.returncode or set(deps.stdout.splitlines()) != {str(PACKAGE/'Init.olean'), str(seed)}:
        raise ValueError(('unexpected direct dependencies', deps.returncode, deps.stdout, deps.stderr))
    after = parent_check()
    if before != after or digest(seed) != digest(PARENT/'FreeJEarlySize.olean') or digest(src) != SOURCE_HASH:
        raise ValueError('input changed during replay')
    data = {'status':'PASS_BOUNDED_FREEJ_GRAPH_V_BOUND', 'lean_exit_code':proc.returncode,
            'lean_command':cmd, 'lean_stdout':proc.stdout, 'lean_stderr':proc.stderr,
            'object_sha256':digest(obj), 'deps_exit_code':deps.returncode, 'deps_stdout':deps.stdout,
            'checked_parent_inputs':before,
            'scope':'Single-author historical model overlay; reused authenticated partial parent closure and package. Not a fresh full-source or package-transitive audit, compact44 calibration, or object-level iPRA proof.'}
    with receipt.open('x') as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write('\n')
    print('PASS_BOUNDED_FREEJ_GRAPH_V_BOUND', digest(receipt))

if __name__ == '__main__':
    main()
