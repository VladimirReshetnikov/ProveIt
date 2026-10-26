#!/usr/bin/env python3
"""Check that the prototype's legacy tables are exact renamings of ProveIt.

This checks source transcription, not the supplied ScalarPRCode backend.
Usage: python3 check_schedule_transcription.py /path/to/ProveIt
"""
from pathlib import Path
import argparse
import hashlib
import json
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('repository', type=Path)
args = parser.parse_args()
source_path = args.repository / ('Computability/DiophantineConsistency/Lean/'
                                'DiophantineConsistency/AnnotatedRuleSchedules.lean')
prototype_path = Path(__file__).resolve().parents[1] / 'lean' / 'StructuralSchedule.lean'
source = source_path.read_text(encoding='utf-8')
prototype = prototype_path.read_text(encoding='utf-8')
legacy = prototype.split('namespace Legacy\n', 1)[1].split('\nend Legacy', 1)[0]

def table_body(text, name):
    match = re.search(r'^def ' + re.escape(name) + r'\b', text, flags=re.M)
    if not match:
        raise ValueError(f'Missing definition: {name}')
    tail = text[match.start():]
    next_decl = re.search(r'\n(?:def|theorem|namespace|end|/--)\b', tail)
    definition = tail[:next_decl.start()] if next_decl else tail
    return definition.split('match tag with', 1)[1].strip()

def tokens(s):
    return re.findall(r'[A-Za-z_][A-Za-z_0-9.]*|\d+|=>|[^\s]', s)

checked = []
for name in ('outputBody', 'premiseBodies'):
    original = table_body(source, name)
    mapped = re.sub(r'\br\.([A-Za-z]+)\b', r'(env .\1)', original)
    for old, new in (
        ('forkCode', 'coding.fork'),
        ('binaryCode', 'binary coding'),
        ('unaryCode', 'unary coding'),
        ('variableCode', 'variableNode coding'),
        ('bottomCode', '(bottom coding)'),
    ):
        mapped = re.sub(r'\b' + old + r'\b', new, mapped)
    target = table_body(legacy, name)
    if tokens(mapped) != tokens(target):
        import difflib
        raise SystemExit('\n'.join(difflib.unified_diff(
            [' '.join(tokens(mapped))], [' '.join(tokens(target))],
            fromfile='source after field/operation renaming',
            tofile='prototype Legacy table', lineterm='')))
    checked.append(name)

print(json.dumps({
    'source': str(source_path),
    'source_sha256': hashlib.sha256(source_path.read_bytes()).hexdigest(),
    'prototype_sha256': hashlib.sha256(prototype_path.read_bytes()).hexdigest(),
    'checked': checked,
    'result': 'exact token equality after documented operation/field renaming',
    'scope': 'numeric table transcription only; no ScalarPRCode AST equality claim'
}, indent=2))
