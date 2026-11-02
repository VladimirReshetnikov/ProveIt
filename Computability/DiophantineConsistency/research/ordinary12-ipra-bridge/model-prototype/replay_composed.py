#!/usr/bin/env python3
"""Fresh bounded replay of the abstract three-factor IΣ₁-model split."""
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
SOURCES = {
    'Ordinary12Residual': '778680f7f431048e05c32742500197852614478a9d6750678a0c3eff4429135d',
    'Ordinary12CarrierExclusions': 'ffc7ed63aa25c39c1dfdcb7266f135839071184b6539031f8f753bd4556f6508',
    'Ordinary12FactorSplit': 'dc6c9d657e1ddc14e8719e27d624810e5cefcdbb3b9a44f911e635fc06448ff5',
    'Ordinary12ComposedSplit': '48af107e56cd2bb9392d549040266e7b7dd0262f26b5b0829077cd6240aea072',
}

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--receipt', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.absolute()
    if output.exists() or output.is_symlink() or args.receipt.exists() or args.receipt.is_symlink():
        raise ValueError('refusing to overwrite output or receipt')
    for name, digest in SOURCES.items():
        if H(HERE / (name + '.lean')) != digest: raise ValueError(('source drift', name))
    inner_script = HERE / 'replay.py'
    inner_hash = H(inner_script)
    output.mkdir(parents=True)
    base = output / 'base'
    inner_receipt = output / 'base-receipt.json'
    inner = subprocess.run([sys.executable, str(inner_script), '--output', str(base), '--receipt', str(inner_receipt)],
                           capture_output=True, text=True)
    if inner.returncode: raise ValueError(('base overlay replay failed', inner.stdout, inner.stderr))
    prior = json.loads(inner_receipt.read_text())
    if prior['status'] != 'PASS_BOUNDED_MODEL_RESIDUE_PROTOTYPE' or prior['attempts'][2]['exit_code'] != 0:
        raise ValueError('base model lemma missing')
    lib = base / 'lib'
    module_dir = lib / 'DiophantineConsistency'
    residual = module_dir / 'Ordinary12Residual.olean'
    if residual.exists() or residual.is_symlink(): raise ValueError('residual object already exists')
    shutil.copyfile(base / 'attempt3/Ordinary12Residual.olean', residual)
    if H(residual) != prior['attempts'][2]['object_sha256']: raise ValueError('residual object changed')
    generated = {'Ordinary12Residual': H(residual)}
    env = os.environ.copy()
    for name in ('LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LD_LIBRARY_PATH', 'LD_PRELOAD', 'LD_AUDIT'):
        env.pop(name, None)
    env['LEAN_PATH'] = str(lib) + ':' + str(PACKAGE)
    rows = []
    for name, reports in [('Ordinary12CarrierExclusions', 2), ('Ordinary12FactorSplit', 2), ('Ordinary12ComposedSplit', 1)]:
        root = output / name / 'src'
        source = root / 'DiophantineConsistency' / (name + '.lean')
        source.parent.mkdir(parents=True)
        shutil.copyfile(HERE / (name + '.lean'), source)
        obj = module_dir / (name + '.olean')
        if obj.exists() or obj.is_symlink(): raise ValueError(('output exists', name))
        command = [str(LEAN), '-M8000', '-j1', '-DElab.async=false', f'--root={root}', str(source), '-o', str(obj)]
        process = subprocess.run(command, env=env, capture_output=True, text=True)
        combined = process.stdout + process.stderr
        if process.returncode or 'sorryAx' in combined or 'warning:' in combined or combined.count('depends on axioms:') != reports:
            raise ValueError(('prototype compilation failed', name, process.stdout, process.stderr))
        deps = subprocess.run([str(LEAN), '--deps', str(source)], env=env, capture_output=True, text=True)
        direct = {
            'Ordinary12CarrierExclusions': ['ArithmeticAdaptiveFactorUnits2011'],
            'Ordinary12FactorSplit': ['Ordinary12Residual'],
            'Ordinary12ComposedSplit': ['Ordinary12CarrierExclusions', 'Ordinary12FactorSplit'],
        }[name]
        expected = {str(PACKAGE / 'Init.olean')} | {str(module_dir / (n + '.olean')) for n in direct}
        if deps.returncode or set(deps.stdout.splitlines()) != expected:
            raise ValueError(('unexpected direct imports', name, deps.stdout, deps.stderr))
        generated[name] = H(obj)
        rows.append({'module': name, 'exit_code': process.returncode, 'stdout': process.stdout, 'stderr': process.stderr,
                     'source_sha256': H(source), 'object_sha256': H(obj), 'direct_deps_stdout': deps.stdout,
                     'direct_deps_exit_code': deps.returncode, 'command': command})
        for earlier, digest in generated.items():
            if H(module_dir / (earlier + '.olean')) != digest: raise ValueError(('generated object drift', earlier))
    if H(inner_script) != inner_hash: raise ValueError('base replay script drift')
    for name, digest in SOURCES.items():
        if H(HERE / (name + '.lean')) != digest: raise ValueError(('source drift', name))
    for link, metadata in prior['seed_links'].items():
        path = Path(link); src = Path(metadata['source'])
        if not path.is_symlink() or path.resolve() != src or H(src) != metadata['sha256']:
            raise ValueError(('historical seed drift', link))
    for name in prior['absent_parent_paths']:
        path = Path(name)
        if path.exists() or path.is_symlink(): raise ValueError(('new parent companion', name))
    result = {'status': 'PASS_BOUNDED_COMPOSED_MODEL_SPLIT', 'base_replay_exit_code': inner.returncode,
              'base_replay_stdout': inner.stdout, 'base_replay_stderr': inner.stderr,
              'base_receipt_sha256': H(inner_receipt), 'base_receipt': prior,
              'generated_objects': generated, 'modules': rows, 'replay_sha256': H(Path(__file__)),
              'scope': 'Single-author exploratory IΣ₁-model abstract factor split, not literal binding, paired guarded project replay, compact44 calibration or iPRA proof.'}
    with args.receipt.open('x') as f:
        json.dump(result, f, indent=2, sort_keys=True); f.write('\n')
    print('PASS_BOUNDED_COMPOSED_MODEL_SPLIT', H(args.receipt))

if __name__ == '__main__':
    main()
