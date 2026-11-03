#!/usr/bin/env python3
"""Check the exact source transformation used by the controller rebuild."""
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
BRIDGE = HERE.parent
ROOT = next(p for p in HERE.parents if (p / 'Computability/BusyBeaver').is_dir())
old = BRIDGE / 'compact44-controller-choice-prototype/ArithmeticControllerChoiceCompact44.lean'
new = HERE / 'ArithmeticControllerChoiceCompact44Triangle.lean'
cantor = ROOT / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ArithmeticCantor.lean'
triangle = HERE / 'CompactControllerTriangle.lean'

def digest(p):
    return sha256(p.read_bytes()).hexdigest()

s = old.read_text()
if s.count('import BusyBeaver.ZFC.ArithmeticCantor') != 1:
    raise ValueError('Unexpected controller import')
s = s.replace('import BusyBeaver.ZFC.ArithmeticCantor', 'import DiophantineConsistency.CompactControllerTriangle')
s = s.replace('namespace DiophantineConsistency.ArithmeticControllerChoiceCompact44',
              'namespace DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle')
s = s.replace('end DiophantineConsistency.ArithmeticControllerChoiceCompact44',
              'end DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle')
s = s.replace('  SetTheory.BusyBeaver.ZFC.ArithmeticCantor', '  CompactControllerTriangle')
s = s.replace('DiophantineConsistency.ArithmeticControllerChoiceCompact44.',
              'DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle.')
if s != new.read_text():
    raise ValueError('Adapted controller does not match the specified transformation')

a, b = cantor.read_text(), triangle.read_text()
for start, stop in [('def triangle (s : V)', 'lemma triangle_double'),
                    ('lemma triangle_double', 'lemma triangle_succ'),
                    ('lemma triangle_succ', 'lemma triangle_mono'),
                    ('lemma le_triangle', 'noncomputable def cantor')]:
    aa = a[a.index(start):a.index(stop, a.index(start))].strip()
    next_marker = {'lemma triangle_mono': 'lemma le_triangle',
                   'noncomputable def cantor': '#print axioms triangle_succ'}.get(stop, stop)
    bb = b[b.index(start):b.index(next_marker, b.index(start))].strip()
    if aa != bb:
        raise ValueError(f'Extracted declaration differs: {start}')
print('PASS exact controller transformation and extracted triangle declarations')
for p in (old, new, cantor, triangle):
    print(digest(p), p)
print('Scope: source comparison only; no independent proof or provider audit')
