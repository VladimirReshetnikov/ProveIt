#!/usr/bin/env python3
"""Generate the formal PA195 source tree from pinned upstream/grammar inputs."""
import hashlib
import json
from pathlib import Path
import re
import sys
from zipfile import ZipFile

root = Path(__file__).resolve().parents[5]
program_path = root / 'Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean'
archive_path = root / 'docs/incoming/pa195_conpa_2026-11-13.zip'
program = program_path.read_bytes()
if hashlib.sha256(program).hexdigest() != '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872':
    raise SystemExit('upstream PA196 Program.lean hash mismatch')
with ZipFile(archive_path) as archive:
    frozen_program = archive.read('pa195_conpa/pa195/vendor/reference/PA196/Program.lean')
    grammar_bytes = archive.read('pa195_conpa/pa195/grammar.json')
if program != frozen_program:
    raise SystemExit('upstream source differs from archive-pinned reference')
if hashlib.sha256(grammar_bytes).hexdigest() != 'b5a4f7beb6a7342ef3f50e949c4b896861e0de4876f8d70e15e8071e6d81ce5f':
    raise SystemExit('PA195 grammar hash mismatch')
grammar = json.loads(grammar_bytes)
rules = grammar['rules']
if len(rules) != 69 or grammar['root'] != 'g68':
    raise SystemExit('unexpected grammar shape')
seen = set()

def emit(value):
    if isinstance(value, str):
        if value in rules and value not in seen:
            raise ValueError('forward/cyclic grammar reference: ' + value)
        if value not in rules and not re.fullmatch(r'node(?:49|55|58|65|70|72|75|142|150)', value):
            raise ValueError('unexpected upstream macro reference: ' + value)
        return value
    if isinstance(value, list) and len(value) == 3 and value[0] == 'leaf':
        if value[1] not in ('inc', 'dec', 'breakTo', 'continueTo') or not isinstance(value[2], int) or value[2] < 0:
            raise ValueError('invalid leaf')
        return f'(.leaf (.{value[1]} {value[2]}))'
    if isinstance(value, list) and len(value) == 2:
        return f'(.node {emit(value[0])} {emit(value[1])})'
    raise ValueError('invalid grammar term')

rendered = []
for name, body in rules.items():
    if not re.fullmatch(r'g[0-9]+', name):
        raise SystemExit('invalid rule name')
    rendered.append(f'def {name} : Tree := {emit(body)}')
    seen.add(name)
text = program.decode()
old = 'def x67 : Tree := .node x3 x66'
if text.count(old) != 1 or text.count('def sites : Array Site') != 1:
    raise SystemExit('unexpected upstream source layout')
text = text[:text.index('def sites : Array Site')]
text = text.replace(old, '\n'.join(rendered) + '\ndef x67 : Tree := ' + grammar['root'])
text = text.replace('namespace PA196.Program', 'namespace PA195.SourceTree')
text += '\nend PA195.SourceTree\n'
if len(sys.argv) != 2:
    raise SystemExit('usage: generate.py OUTPUT.lean')
Path(sys.argv[1]).write_text(text)
print('Generated pinned PA195 source tree:', sys.argv[1])
