#!/usr/bin/env python3
"""Generate the PA194 formal source tree from pinned upstream and grammar."""
import hashlib
import json
from pathlib import Path
import re
import sys
from zipfile import ZipFile

root = Path(__file__).resolve().parents[5]
program_path = root / 'Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/PA196/Program.lean'
archive_path = root / 'docs/incoming/pa194_conpa_2026-11-13.zip'
program = program_path.read_bytes()
if hashlib.sha256(program).hexdigest() != '8c7c6c6884ecbb8f56e893404bb81162db15ef3dd6fd3212881a93994d63d872':
    raise SystemExit('upstream PA196 Program.lean hash mismatch')
with ZipFile(archive_path) as z:
    frozen_program = z.read('pa194_conpa/construction/reference/PA196/Program.lean')
    grammar_bytes = z.read('pa194_conpa/construction/source/pa194.grammar.json')
if program != frozen_program:
    raise SystemExit('upstream source differs from packet reference')
if hashlib.sha256(grammar_bytes).hexdigest() != 'ca78fcfb8394f09eea1ed0d2fdf8fbabd8b4f5ac524f742ba9c45f4b69c1915f':
    raise SystemExit('PA194 grammar hash mismatch')
grammar = json.loads(grammar_bytes)
rules = grammar['rules']
if len(rules) != 68 or grammar['root'] != 'g219445':
    raise SystemExit('unexpected PA194 grammar shape')
ordered = []
visiting = set()
seen = set()

def visit(name):
    if name in seen:
        return
    if name in visiting or name not in rules or not re.fullmatch(r'g[0-9]+', name):
        raise ValueError('cyclic, missing, or invalid rule: ' + name)
    visiting.add(name)
    for value in rules[name]:
        if isinstance(value, str) and value in rules:
            visit(value)
    visiting.remove(name)
    seen.add(name)
    ordered.append(name)
visit(grammar['root'])
if seen != set(rules):
    raise SystemExit('unreachable grammar rules')

def emit(value):
    if isinstance(value, str):
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
rendered = [f'def {name} : Tree := {emit(rules[name])}' for name in ordered]
text = program.decode()
old = 'def x67 : Tree := .node x3 x66'
if text.count(old) != 1 or text.count('def sites : Array Site') != 1:
    raise SystemExit('unexpected upstream source layout')
text = text[:text.index('def sites : Array Site')]
text = text.replace(old, '\n'.join(rendered) + '\ndef x67 : Tree := ' + grammar['root'])
text = text.replace('namespace PA196.Program', 'namespace PA194.SourceTree')
text += '\nend PA194.SourceTree\n'
if len(sys.argv) != 2:
    raise SystemExit('usage: generate.py OUTPUT.lean')
Path(sys.argv[1]).write_text(text)
print('Generated pinned PA194 source tree:', sys.argv[1])
