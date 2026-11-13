#!/usr/bin/env python3
"""Replay the small signed-residue lemma on an isolated historical overlay."""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('replay guards require Python assertions enabled')
HERE = Path(__file__).resolve().parent
PARENT = Path('/tmp/ipra-aq29-fresh-project-pair')
SNAPSHOT = Path('/tmp/ipra-aq29-fresh-source-closure-v2')
PACKAGE = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
PROVIDER = Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/build-all-receipt.json')
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
PIN = {
    PARENT / 'pair-state.json': '04832cc18c11ad9da49d2cfc0c865baed07a18ace44d1de9d8319b150890e7dd',
    SNAPSHOT / 'manifest.json': '63b846158674d41beeaa99843d92008465f8e0fe5c45bb9e1fed4b78e1a2ab48',
    PROVIDER: '7cbd49b6d84497c46520e908fc8c4dc105d7a0070fd1323c6c28e26bf4cf00f6',
    LEAN: 'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550',
}
sources = [HERE / 'failed/attempt01.lean', HERE / 'failed/attempt02.lean', HERE / 'Ordinary12Residual.lean']
source_pins = ['b716d837b4143609941e58ac83beda081f6cbae1f5694641a995f7556c77ac69',
               '600ccc76c6c0db9b67e048f78bc23289285f54f997d01225cd8197e4cf561a96',
               '778680f7f431048e05c32742500197852614478a9d6750678a0c3eff4429135d']

def verify_fixed():
    for path, digest in PIN.items():
        if H(path) != digest: raise ValueError(('fixed input drift', str(path)))
    for path, digest in zip(sources, source_pins):
        if H(path) != digest: raise ValueError(('prototype source drift', str(path)))

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    verify_fixed()
    output = args.output.absolute()
    if output.exists() or output.is_symlink() or args.receipt.exists() or args.receipt.is_symlink():
        raise ValueError('refusing to overwrite output or receipt')
    for protected in (PARENT, SNAPSHOT, PACKAGE, PROVIDER.parent, HERE):
        if output.resolve().is_relative_to(protected.resolve()) or protected.resolve().is_relative_to(output.resolve()):
            raise ValueError(('output overlaps protected path', str(protected)))
    pair = json.loads((PARENT / 'pair-state.json').read_text())
    row = next(x for x in pair['runs'] if x['label'] == 'author')
    state_path = PARENT / 'author/state.json'
    if pair['status'] != 'MATCHED_PASS' or row['exit'] != 0 or H(state_path) != row['builder_state_sha256']:
        raise ValueError('historical matched author parent required')
    state_hash = H(state_path)
    state = json.loads(state_path.read_text())
    manifest = json.loads((SNAPSHOT / 'manifest.json').read_text())
    if state['status'] != 'PASS': raise ValueError('parent state not PASS')
    seen, todo = set(), ['DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011']
    while todo:
        name = todo.pop()
        if name in seen or name not in manifest['sources']: continue
        seen.add(name)
        entry = manifest['sources'][name]
        if H(SNAPSHOT / entry['snapshot_path']) != entry['sha256']:
            raise ValueError(('frozen source drift', name))
        todo.extend(entry['imports'])
    if len(seen) != 20: raise ValueError('unexpected project closure size')
    output.mkdir(parents=True)
    lib = output / 'lib'
    lib.mkdir()
    parent_lib = PARENT / 'author/lib'
    present, absent = {}, []
    for name in sorted(seen):
        for path, metadata in state['outputs'][name].items():
            src = Path(path)
            if not src.is_relative_to(parent_lib): raise ValueError('parent output path escape')
            dst = lib / src.relative_to(parent_lib)
            if metadata is None:
                if src.exists() or src.is_symlink(): raise ValueError(('unexpected companion', path))
                absent.append(path)
            else:
                if src.is_symlink() or not src.is_file() or str(src.resolve()) != metadata['realpath'] or H(src) != metadata['sha256']:
                    raise ValueError(('parent object drift', path))
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.symlink_to(src)
                present[str(dst)] = {'source': str(src), 'sha256': metadata['sha256']}
    env = os.environ.copy()
    for name in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(name, None)
    env['LEAN_PATH'] = str(lib) + ':' + str(PACKAGE)
    rows = []
    for i, source in enumerate(sources, 1):
        root = output / f'attempt{i}' / 'src'
        target = root / 'DiophantineConsistency/Ordinary12Residual.lean'
        target.parent.mkdir(parents=True)
        shutil.copyfile(source, target)
        obj = output / f'attempt{i}' / 'Ordinary12Residual.olean'
        command = [str(LEAN), '-M8000', '-j1', '-DElab.async=false', f'--root={root}', str(target), '-o', str(obj)]
        process = subprocess.run(command, env=env, capture_output=True, text=True)
        if (i < 3 and (process.returncode == 0 or 'Type mismatch' not in process.stdout + process.stderr)):
            raise ValueError(('expected failure missing', i, process.stdout, process.stderr))
        if i == 3 and (process.returncode != 0 or 'sorryAx' in process.stdout + process.stderr or
                       "ordinary_factor_ne_negative_one' depends on axioms:" not in process.stdout):
            raise ValueError(('final prototype did not compile cleanly', process.stdout, process.stderr))
        rows.append({'attempt': i, 'exit_code': process.returncode, 'stdout': process.stdout,
                     'stderr': process.stderr, 'source_sha256': H(target),
                     'object_sha256': H(obj) if obj.is_file() else None, 'command': command})
    deps = subprocess.run([str(LEAN), '--deps', str(output / 'attempt3/src/DiophantineConsistency/Ordinary12Residual.lean')],
                          env=env, capture_output=True, text=True)
    expected = {str(PACKAGE / 'Init.olean'), str(lib / 'DiophantineConsistency/ArithmeticAdaptiveFactorUnits2011.olean')}
    if deps.returncode or set(deps.stdout.splitlines()) != expected:
        raise ValueError(('unexpected direct deps', deps.returncode, deps.stdout, deps.stderr))
    verify_fixed()
    if H(state_path) != state_hash: raise ValueError('parent state drift')
    for name in seen:
        entry = manifest['sources'][name]
        if H(SNAPSHOT / entry['snapshot_path']) != entry['sha256']: raise ValueError(('frozen source drift', name))
    for link, metadata in present.items():
        path = Path(link); src = Path(metadata['source'])
        if not path.is_symlink() or path.resolve() != src or H(src) != metadata['sha256']:
            raise ValueError(('seed drift', link))
    for name in absent:
        path = Path(name)
        if path.exists() or path.is_symlink(): raise ValueError(('new parent companion', name))
    result = {'status': 'PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE', 'parent_pair_sha256': PIN[PARENT / 'pair-state.json'],
              'parent_state_sha256': state_hash, 'snapshot_sha256': PIN[SNAPSHOT / 'manifest.json'],
              'provider_sha256': PIN[PROVIDER], 'lean_sha256': PIN[LEAN], 'project_modules': sorted(seen),
              'seed_links': present, 'absent_parent_paths': absent, 'attempts': rows,
              'direct_deps_exit_code': deps.returncode, 'direct_deps_stdout': deps.stdout,
              'replay_sha256': H(Path(__file__)),
              'scope': 'Isolated single-author source-declared closure prototype; not paired guarded project replay, full package/dynamic ancestry, literal 12-variable split, or iPRA proof.'}
    with args.receipt.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print('PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE', H(args.receipt))

if __name__ == '__main__':
    main()
