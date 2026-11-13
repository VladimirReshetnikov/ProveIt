#!/usr/bin/env python3
"""Use a temporary Git repository to test the package-choice gate."""
import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

if not __debug__:
    raise RuntimeError('package-choice controls require Python assertions enabled')
HERE = Path(__file__).resolve().parent
names = ('DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral',
         'DiophantineConsistency.IPRASquareSumsNative')
with tempfile.TemporaryDirectory(prefix='frontier13-choice-toy-') as temp:
    root = Path(temp)
    def git(*args):
        return subprocess.check_output(['git', *args], cwd=root, text=True).strip()
    git('init', '-q')
    script = root / 'Computability/DiophantineConsistency/research/ipra-selected-refutation-verifier/historical/check_package_choice.py'
    script.parent.mkdir(parents=True)
    shutil.copyfile(HERE / 'check_package_choice.py', script)
    sources = {}
    for name in names:
        package = 'Computability/DiophantineConsistency/Lean/' + name.replace('.', '/') + '.lean'
        draft = 'draft/' + name.split('.')[-1] + '.lean'
        raw = ('-- ' + name + '\n').encode()
        for path in (package, draft):
            (root / path).parent.mkdir(parents=True, exist_ok=True)
            (root / path).write_bytes(raw)
        sources[name] = {'workspace_path': draft, 'sha256': hashlib.sha256(raw).hexdigest(), 'imports': []}
    git('add', '.')
    git('-c', 'user.name=Toy', '-c', 'user.email=toy@example.invalid', 'commit', '-qm', 'pinned drafts and package sources')
    source_commit = git('rev-parse', 'HEAD')
    manifest = script.parent.parent / 'author-additions.json'
    manifest.write_text(json.dumps({'source_commit': source_commit, 'sources': sources}))
    chosen = {n: dict(row, workspace_path='Computability/DiophantineConsistency/Lean/' + n.replace('.', '/') + '.lean') for n, row in sources.items()}
    policy = script.parent / 'task-policy.json'
    policy.write_text(json.dumps({'sources': chosen}))
    git('add', '.')
    git('-c', 'user.name=Toy', '-c', 'user.email=toy@example.invalid', 'commit', '-qm', 'task policy')
    def run(*flags):
        return subprocess.run([sys.executable, *flags, str(script)], cwd=root, capture_output=True, text=True)
    assert run().returncode == 0
    package = root / chosen[names[0]]['workspace_path']
    original = package.read_bytes()
    package.write_bytes(original + b'-- drift\n')
    assert run().returncode != 0
    package.write_bytes(original)
    raw_policy = policy.read_text()
    bad = json.loads(raw_policy)
    bad['sources'][names[0]]['workspace_path'] = sources[names[0]]['workspace_path']
    policy.write_text(json.dumps(bad))
    assert run().returncode != 0
    policy.write_text(raw_policy)
    raw_manifest = manifest.read_text()
    bad = json.loads(raw_manifest)
    bad['sources'][names[0]]['sha256'] = '0' * 64
    manifest.write_text(json.dumps(bad))
    assert run().returncode != 0
    manifest.write_text(raw_manifest)
    assert run('-O').returncode != 0
print('PASS_TRACKED_PACKAGE_CHOICE_TOY baseline, source drift, wrong path, hash drift, optimized mode')
