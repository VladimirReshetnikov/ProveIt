#!/usr/bin/env python3
"""Deterministic positive register lift of the frozen 13-variable circuit.

The introduced positive coordinate E is constrained by E=X*Y.  This changes
the degree presentation without changing any original integer zero.
"""
import hashlib
import json
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
source_path = ROOT / 'p13_degree28.json'
expected = '1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49'
if hashlib.sha256(source_path.read_bytes()).hexdigest() != expected:
    raise RuntimeError('Frozen P13 source digest mismatch')
p = json.loads(source_path.read_text())
p['name'] = 'positive_register_lift_14_degree24'
p['witnesses'].append('E')
rows = p['source']
matches = [row for row in rows if row[0] == 'E']
if matches != [['E', '*', 'X', 'Y']]:
    raise RuntimeError('Unexpected source E definition')
matches[0][0] = 'Eprod'
last_residual = max(j for j, row in enumerate(rows) if row[0] in p['residuals'])
rows.insert(last_residual + 1, ['AE', '-', 'E', 'Eprod'])
rows.extend([['AE2', '*', 'AE', 'AE'], ['P14', '+', p['output'], 'AE2']])
p['residuals'].append('AE')
p['output'] = 'P14'
p['operations'] = len(rows)
p['system_operations'] = 92
p['operation_breakdown'] = dict(Counter(row[1] for row in rows))
p['residual_degrees'] = [12, 11, 12, 12, 2]
p['exact_degree'] = 24
p.pop('leading_form')
p['selected_monomial'] = 'i^4*eta^8*E^4*Y^8'
p['selected_coefficient'] = '81*beta^4'
p['source_circuit_sha256'] = expected
p['proof_status'] = 'Unique positive coordinate lift of frozen P13; no additional inherited source assumption'
(ROOT / 'p14_degree24.json').write_text(json.dumps(p, indent=2) + '\n')
print(json.dumps({'operations': len(rows), 'sha256': hashlib.sha256((ROOT/'p14_degree24.json').read_bytes()).hexdigest()}, indent=2))
