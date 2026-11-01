#!/usr/bin/env python3
"""Exercise the real preparer against a matched pair of tiny real Lean builds."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
TOOLS = HERE.parent/'fresh-project-closure'
LEAN = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
TOOL = LEAN.parent.parent/'lib/lean'
H = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

def command(*args, cwd=None):
    p = subprocess.run(list(map(str, args)), cwd=cwd, capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError((args, p.returncode, p.stdout, p.stderr))
    return p

with tempfile.TemporaryDirectory(prefix='fresh-project-rebase-control-') as td:
    root = Path(td); workspace = root/'workspace'; workspace.mkdir()
    command('git', 'init', '-q', cwd=workspace)
    (workspace/'lakefile.toml').write_text('name = "Toy"\n')
    (workspace/'lean-toolchain').write_text('leanprover/lean4:v4.32.0\n')
    texts = {'Toy.A': 'def changedValue : Nat := 1\n',
             'Toy.Independent': 'def independentValue : Nat := 7\n',
             'Toy.Check': 'import Toy.A\nimport Toy.Independent\ntheorem toyCheck : changedValue = 1 := rfl\n#print axioms toyCheck\n'}
    imports = {'Toy.A': [], 'Toy.Independent': [], 'Toy.Check': ['Toy.A', 'Toy.Independent']}
    def commit():
        command('git', 'add', '.', cwd=workspace)
        command('git', '-c', 'user.name=Toy', '-c', 'user.email=toy@example.invalid',
                'commit', '-q', '-m', 'toy', cwd=workspace)
    def write_sources():
        for name, text in texts.items():
            p = workspace/'src'/(name.replace('.', '/')+'.lean')
            p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
    def snapshot(path):
        rows = {}
        for name, text in texts.items():
            p = path/'src'/(name.replace('.', '/')+'.lean')
            p.parent.mkdir(parents=True, exist_ok=True); p.write_text(text)
            rows[name] = {'workspace_path': str(p.relative_to(path)),
                          'snapshot_path': str(p.relative_to(path)),
                          'sha256': H(p), 'imports': imports[name]}
        manifest = {'status': 'FROZEN_NOT_COMPILED', 'root': str(workspace),
                    'target': 'Toy.Check', 'order': list(texts), 'project_modules': len(texts),
                    'sources': rows, 'lakefile_sha256': H(workspace/'lakefile.toml'),
                    'lean_toolchain_sha256': H(workspace/'lean-toolchain')}
        (path/'manifest.json').write_text(json.dumps(manifest))
    write_sources(); commit(); old = root/'old'; snapshot(old)
    provider = root/'provider'; foundation = provider/'.lake/build/lib/lean/Foundation'; foundation.mkdir(parents=True)
    pkg = provider/'package-lib'; pkg.mkdir(); (pkg/'Foundation').symlink_to(foundation)
    for name in ('Init', 'Init.olean', 'Init.ir', 'Init.olean.private', 'Init.olean.server'):
        source = TOOL/name
        if source.exists(): (pkg/name).symlink_to(source, target_is_directory=source.is_dir())
    foundation_input = provider/'input.json'; foundation_input.write_text(json.dumps({'lean_sha256': H(LEAN)}))
    receipt = provider/'receipt.json'; receipt.write_text(json.dumps({
        'manifest_sha256': H(foundation_input), 'status': 'BUILT', 'exit_code': 0,
        'declared_external_guard': {}, 'overlay': str(pkg), 'root': str(provider),
        'foundation_artifacts': {}}))
    pair = root/'parent'
    p = command(sys.executable, TOOLS/'run_pair.py', '--snapshot', old,
                '--snapshot-sha256', H(old/'manifest.json'), '--provider-receipt', receipt,
                '--provider-sha256', H(receipt), '--foundation-input', foundation_input,
                '--expected-axiom-reports', '1', '--output', pair)
    pair_state = pair/'pair-state.json'
    observation = root/'observation.json'; observation.write_text(json.dumps({
        'observed_exit_code': p.returncode, 'observed_stdout': p.stdout,
        'pair_state_sha256': H(pair_state), 'pair_state_path': str(pair_state)}))
    texts['Toy.A'] = 'def changedValue : Nat := 2\n'
    texts['Toy.Check'] = texts['Toy.Check'].replace('= 1', '= 2')
    write_sources(); commit(); new = root/'new'; snapshot(new)
    args = [sys.executable, HERE/'prepare.py', '--parent', pair, '--old-snapshot', old,
            '--new-snapshot', new, '--old-sha256', H(old/'manifest.json'),
            '--new-sha256', H(new/'manifest.json'), '--parent-pair-sha256', H(pair_state),
            '--parent-observation', observation, '--parent-observation-sha256', H(observation)]
    out = root/'successor'; command(*args, '--output', out)
    result = json.loads((out/'preparation.json').read_text())
    assert result['status'] == 'PREPARED_NOT_REBUILT'
    assert result['plan']['affected'] == ['Toy.A', 'Toy.Check']
    assert result['plan']['unaffected'] == ['Toy.Independent']
    for label in ('author', 'peer'):
        assert (out/label/'lib/Toy/Independent.olean').is_file()
        assert not (out/label/'lib/Toy/A.olean').exists()
        assert not (out/label/'lib/Toy/Check.olean').exists()
    original_peer = (out/'peer/lib/Toy/Independent.olean').read_bytes()
    (out/'author/lib/Toy/Independent.olean').write_bytes(b'disturbed')
    assert (out/'peer/lib/Toy/Independent.olean').read_bytes() == original_peer
    bad = json.loads(observation.read_text()); bad['observed_exit_code'] = None
    observation.write_text(json.dumps(bad)); bad_args = args[:]
    bad_args[bad_args.index('--parent-observation-sha256')+1] = H(observation)
    q = subprocess.run([*map(str, bad_args), '--output', str(root/'bad')], capture_output=True, text=True)
    assert q.returncode != 0 and not (root/'bad').exists()
print('PASS: real Lean matched toy pair, isolated unaffected seeds, affected exclusion and unobserved-exit rejection')
