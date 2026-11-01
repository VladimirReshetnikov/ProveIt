#!/usr/bin/env python3
"""Freeze and compare two completed balance-shift Lean replay packets."""
import hashlib
import json
from pathlib import Path
import shutil
import sys

if len(sys.argv) != 4:
    raise SystemExit('usage: freeze_balance_replay.py AUTHOR PEER OUTPUT')
author, peer, output = map(Path, sys.argv[1:])
if author.resolve() == peer.resolve() or output.exists():
    raise ValueError('distinct runs and a new output directory are required')
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
states = [json.loads((p / 'state.json').read_text()) for p in (author, peer)]
a, b = states
if a['status'] != 'PASS' or b['status'] != 'PASS':
    raise ValueError('both replays must have passed')
if a['anchors'] != b['anchors'] or a['boundary'] != b['boundary'] or a['provider'] != b['provider']:
    raise ValueError('replay inputs differ')
if a['records'] != b['records']:
    raise ValueError('source, object, log, exit or warning rows differ')
for name, expected in a['anchors'].items():
    if sha(name) != expected:
        raise ValueError(('guard changed', name))
for root, state in zip((author, peer), states):
    for row in state['records']:
        name = row['module']
        for path, key in ((root / 'src/DiophantineConsistency' / (name+'.lean'), 'source_sha256'),
                          (root / 'lib/DiophantineConsistency' / (name+'.olean'), 'object_sha256'),
                          (root / 'logs' / (name+'.log'), 'log_sha256')):
            if sha(path) != row[key]:
                raise ValueError(('output hash changed', str(path)))
        if row['exit'] != 0 or row['warnings'] != 0:
            raise ValueError(('failed or warning-bearing row', name))
for row in a['records']:
    name = row['module']
    for directory, suffix in (('src/DiophantineConsistency', '.lean'), ('logs', '.log')):
        if (author / directory / (name+suffix)).read_bytes() != (peer / directory / (name+suffix)).read_bytes():
            raise ValueError(('replay bytes differ', name, directory))
output.mkdir(parents=True)
for label, root in (('author', author), ('peer', peer)):
    dest = output / label
    (dest / 'src').mkdir(parents=True)
    (dest / 'logs').mkdir()
    shutil.copyfile(root / 'state.json', dest / 'state.json')
    for row in a['records']:
        name = row['module']
        shutil.copyfile(root / 'src/DiophantineConsistency' / (name+'.lean'), dest / 'src' / (name+'.lean'))
        shutil.copyfile(root / 'logs' / (name+'.log'), dest / 'logs' / (name+'.log'))
receipt = {'status': 'MATCHED_PASS', 'author': str(author), 'peer': str(peer),
           'rows': a['records'], 'guarded_project_files': a['parent_project_object_count'],
           'provider': a['provider'], 'author_state_sha256': sha(author/'state.json'),
           'peer_state_sha256': sha(peer/'state.json'),
           'freezer_sha256': sha(__file__), 'scope': a['scope']}
(output / 'comparison.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
print('MATCHED_PASS', len(a['records']), 'rows;', a['parent_project_object_count'], 'guarded project files')
