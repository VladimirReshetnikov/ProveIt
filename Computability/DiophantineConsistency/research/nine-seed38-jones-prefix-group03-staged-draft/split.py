#!/usr/bin/env python3
"""Mechanically split the six candidate lemmas into four small Lean modules."""
import hashlib
import json
import re
import sys
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
P = Path(__file__).resolve().parent
D = P.parent.parent
original = D / 'research/nine-seed38-jones-prefix-group03-draft/Norm38MacroPrefixGroup03.lean'
if hashlib.sha256(original.read_bytes()).hexdigest() != '465982c11f7c198ed03909354c006ac453f44ff23f8ebed663e43519774d5c7d':
    raise RuntimeError('original source hash')
s = original.read_text()
names = ['d8_B', 'd9_B', 'd9_b', 'prefix_g', 'prefix_theta', 'prefix_G']
blocks = re.findall(r'(?ms)^theorem (\w+)\b.*?(?=^theorem |^#print axioms )', s)
if blocks != names:
    raise RuntimeError(('theorem inventory', blocks))
parts = {}
for name in names:
    m = re.search(r'(?ms)^theorem ' + re.escape(name) + r'\b.*?(?=^theorem |^#print axioms )', s)
    if m is None:
        raise RuntimeError(('missing theorem', name))
    parts[name] = m.group(0).rstrip()
header = ['set_option autoImplicit false', 'noncomputable section',
          'namespace DiophantineConsistency.Norm38MacroPrefixGroup03',
          'open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01 Norm38MacroPrefixGroup02 ExecutableJones', '']
groups = (
    ('Norm38MacroPrefixCarry03', 'DiophantineConsistency.Norm38MacroPrefixCarry', names[:3]),
    ('Norm38MacroPrefixGsmall', 'DiophantineConsistency.Norm38MacroPrefixCarry03', names[3:4]),
    ('Norm38MacroPrefixTheta', 'DiophantineConsistency.Norm38MacroPrefixCarry03', names[4:5]),
    ('Norm38MacroPrefixGlarge', 'DiophantineConsistency.Norm38MacroPrefixCarry03', names[5:6]),
)
digests = {}
for module, imp, selected in groups:
    lines = ['import ' + imp, '', '/-! Mechanical source split; Lean result not implied. -/'] + header
    for name in selected:
        lines += [parts[name], '']
    lines += [f'#print axioms {name}' for name in selected]
    lines += ['end DiophantineConsistency.Norm38MacroPrefixGroup03']
    encoded = ('\n'.join(lines) + '\n').encode()
    out = P / (module + '.lean')
    if sys.argv[1:] == ['--write']:
        with out.open('xb') as f: f.write(encoded)
    elif sys.argv[1:] == ['--check']:
        if out.read_bytes() != encoded: raise RuntimeError(('split differs', module))
    else:
        raise SystemExit('expected --write or --check')
    digests[module] = hashlib.sha256(encoded).hexdigest()
if sys.argv[1:] == ['--check']:
    print(json.dumps({'status': 'PASS_MECHANICAL_STAGE_SPLIT_ONLY', 'modules': digests,
                      'scope': 'Identical theorem text, not Lean compilation or semantic equality.'}, sort_keys=True))
