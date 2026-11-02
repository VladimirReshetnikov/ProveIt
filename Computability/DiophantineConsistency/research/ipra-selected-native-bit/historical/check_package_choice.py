#!/usr/bin/env python3
"""Bind the two selected tracked package sources to the guarded author drafts."""
import hashlib
import json
import subprocess
from pathlib import Path

if not __debug__:
    raise RuntimeError('package-choice checks require Python assertions enabled')
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
policy = json.loads((HERE / 'task-policy.json').read_text())
manifest = json.loads((HERE.parent / 'author-additions.json').read_text())
H = lambda raw: hashlib.sha256(raw).hexdigest()
names = ('DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral',
         'DiophantineConsistency.IPRASquareSumsNative')
for name in names:
    author = manifest['sources'][name]
    chosen = policy['sources'][name]
    path = 'Computability/DiophantineConsistency/Lean/' + name.replace('.', '/') + '.lean'
    assert chosen['workspace_path'] == path and chosen['sha256'] == author['sha256']
    assert chosen['imports'] == author['imports']
    tracked = subprocess.check_output(['git', 'ls-files', '--error-unmatch', '--', path], cwd=ROOT, text=True).strip()
    assert tracked == path
    subprocess.run(['git', 'diff', '--quiet', 'HEAD', '--', path], cwd=ROOT, check=True)
    head_blob = subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=ROOT)
    author_blob = subprocess.check_output(['git', 'show', manifest['source_commit'] + ':' + author['workspace_path']], cwd=ROOT)
    assert H((ROOT / path).read_bytes()) == H(head_blob) == H(author_blob) == author['sha256']
print('PASS_TRACKED_PACKAGE_CHOICE 2 author draft hashes match HEAD and workspace')
