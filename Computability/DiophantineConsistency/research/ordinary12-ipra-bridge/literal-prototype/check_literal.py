#!/usr/bin/env python3
"""Check the Lean literal against every row of the pinned ordinary12 graph."""
import hashlib
import json
import re
from pathlib import Path

if not __debug__:
    raise RuntimeError('literal checks require Python assertions enabled')
HERE = Path(__file__).resolve().parent
candidate_path = HERE.parents[1] / 'ordinary-unit-products/p12_ordinary_degree70.json'
raw = candidate_path.read_bytes()
assert hashlib.sha256(raw).hexdigest() == '444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010'
candidate = json.loads(raw)
assert len(candidate['source']) == 100 and len(candidate['witnesses']) == 12
assert candidate['fixed_numerals'] == ['beta', 'K0', 'MC', 'MF'] and candidate['output'] == 'P12'

def validate(text):
    inputs = re.findall(r'^  let (\w+) : Expr \(Fin 12\) := \.var (\d+)$', text, re.M)
    ports = re.findall(r'^  let (\w+) : Expr \(Fin 12\) := \.constant \(p (\d+)\)$', text, re.M)
    if inputs != [(n, str(i)) for i, n in enumerate(candidate['witnesses'])]:
        raise ValueError('input aliases')
    if ports != [(n, str(i)) for i, n in enumerate(candidate['fixed_numerals'])]:
        raise ValueError('port aliases')
    if text.count('  -- BEGIN LITERAL GRAPH\n') != 1 or text.count('  -- END LITERAL GRAPH\n') != 1:
        raise ValueError('graph markers')
    body = text.split('  -- BEGIN LITERAL GRAPH\n', 1)[1].split('  -- END LITERAL GRAPH\n', 1)[0]
    rows = []
    for line in body.splitlines():
        m = re.fullmatch(r'  let (\w+) := (\w+) ([+*\-]) (\w+)', line)
        if not m: raise ValueError(('invalid row', line))
        name, left, op, right = m.groups()
        atom = lambda x: int(x) if x.isdecimal() else x
        rows.append([name, op, atom(left), atom(right)])
    if rows != candidate['source']: raise ValueError('graph rows')
    if text.count('  ⟨g94, g95, g97, P12⟩\n') != 1: raise ValueError('factor/output aliases')
    return len(rows)

source = (HERE / 'Ordinary12Literal.lean').read_text()
assert hashlib.sha256(source.encode()).hexdigest() == '23a22eebc33d262e1b4c134c6072e808c002aac31a627def951bc753d3e96709'
assert validate(source) == 100
mutations = [
    ('  let g0 := 6 * j\n', '  let g0 := 6 + j\n'),
    ('  let j : Expr (Fin 12) := .var 0\n', '  let j : Expr (Fin 12) := .var 1\n'),
    ('  let beta : Expr (Fin 12) := .constant (p 0)\n', '  let beta : Expr (Fin 12) := .constant (p 1)\n'),
    ('  ⟨g94, g95, g97, P12⟩\n', '  ⟨g95, g95, g97, P12⟩\n'),
]
for before, after in mutations:
    assert source.count(before) == 1
    try:
        validate(source.replace(before, after))
    except ValueError:
        pass
    else:
        raise RuntimeError(('mutation accepted', before))
print('PASS_ORDINARY12_LITERAL_GRAPH 100 rows 12 inputs 4 ports 4 mutations rejected')
