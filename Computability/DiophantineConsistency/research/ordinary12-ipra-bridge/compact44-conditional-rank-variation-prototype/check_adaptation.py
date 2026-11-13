#!/usr/bin/env python3
"""Check source adaptation of the generic packing variation theorem."""
from hashlib import sha256
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROJECT = next(p for p in HERE.parents if (p / 'Lean/DiophantineConsistency').is_dir())
old = PROJECT / 'Lean/DiophantineConsistency/ArithmeticConstructionVariation.lean'
new = HERE / 'ArithmeticConstructionVariationCompact44.lean'
s = old.read_text()
replacements = [
    ('import DiophantineConsistency.ArithmeticControllerChoice',
     'import DiophantineConsistency.ArithmeticControllerChoiceCompact44Triangle'),
    ('ArithmeticControllerData.one_lt_exp', 'ArithmeticControllerDataCompact44.one_lt_exp'),
    ('ArithmeticControllerChoice.bsum_zero_fn', 'ArithmeticControllerChoiceCompact44Triangle.bsum_zero_fn'),
    ('namespace DiophantineConsistency.ArithmeticConstructionVariation',
     'namespace DiophantineConsistency.ArithmeticConstructionVariationCompact44'),
    ('end DiophantineConsistency.ArithmeticConstructionVariation',
     'end DiophantineConsistency.ArithmeticConstructionVariationCompact44'),
]
for a, b in replacements:
    if s.count(a) != 1:
        raise ValueError(f'Unexpected occurrence count: {a}')
    s = s.replace(a, b)
if s != new.read_text():
    raise ValueError('Adapted source differs from stated substitutions')
for p in (old, new):
    print(sha256(p.read_bytes()).hexdigest(), p)
print('PASS exact import, generic lemma and namespace adaptations')
print('Scope: external source comparison, not an independent proof or provider audit')
