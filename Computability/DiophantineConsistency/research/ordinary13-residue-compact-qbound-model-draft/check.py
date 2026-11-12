#!/usr/bin/env python3
"""Read-only source pins and bounded arithmetic controls; never runs Lean."""
from pathlib import Path
import hashlib, json
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
pins = json.loads((HERE/'pins.json').read_text())
for path, expected in pins.items():
    assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest() == expected, path

def source(path): return (ROOT/path).read_text()
draft = source('research/ordinary13-residue-compact-qbound-model-draft/ResidueCompactQBound.lean.src')
beta = source('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean')
ports = source('Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean')
q = source('research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src')
power = source('research/ordinary13-residue-witness-pell-model-draft/ResiduePellCoordinates.lean.src')
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta
assert 67*8807 == 590069 and 6 < 590069 and 2**6 == 64 and 46 < 64
assert 'def ports (β K L H : ℕ) : Fin 4 → ℕ := ![β,K,L,β+H]' in ports
assert 'def q (p : Fin 4 → ℕ) (v : Fin 13 → V) : V := 1+v 0*(p 0:V)' in q
assert '(hq46 : 46≤q p v)' in power
for snippet in ['CompactFixedBeta.beta_identity', 'ArithmeticStandardCasts.cast_exp',
                'exp_monotone_le.mpr', 'pos_iff_one_le.mp hJ',
                'ResiduePellCoordinatesDraft.graph_power (ports K) v hz hJ hb hX hgap hwindow hq']:
    assert snippet in draft, snippet
endpoint = draft.split('theorem compact_graph_power',1)[1].split(':= by',1)[0]
assert '(hq46 :' not in endpoint and '(hbeta :' not in endpoint
for snippet in ['(hz :', '(hJ :', '(hX :', '(hgap :', '(hwindow :']:
    assert snippet in endpoint
controls=0
for b in range(46,101):
    for j in range(1,21):
        assert 1+j*b >= 47
        controls += 1
print(json.dumps({'beta_exponent':590069,'bounded_q_controls':controls,
    'fixed_first_port_source_checked':True, 'lean_executed':False,
    'status':'source-only; no elaboration, proof of provider provenance, or PDF binding',
    'source_pins':pins},sort_keys=True,indent=2))
