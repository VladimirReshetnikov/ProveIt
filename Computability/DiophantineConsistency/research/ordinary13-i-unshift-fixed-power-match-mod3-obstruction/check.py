#!/usr/bin/env python3
"""Replay bounded mod-3 certificate against pinned compact sources and graph."""
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parents[2]
here = Path(__file__).resolve().parent
pins = json.loads((here / 'pins.json').read_text())
for path, expected in pins.items():
    assert hashlib.sha256((root / path).read_bytes()).hexdigest() == expected, path

def contains(path, pieces):
    source = (root / path).read_text()
    for piece in pieces:
        assert piece in source, (path, piece)

mask = 'Lean/DiophantineConsistency/Compact44/CompactConcreteMask.lean'
high = 'Lean/DiophantineConsistency/Compact44/CompactHighPopulation.lean'
ports = 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean'
fixed_beta = 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean'
contains(fixed_beta, ['def betaNat : ℕ := 2^(67*8807)-1'])
contains(mask, ['range 943 ∪ Ico 983 993 ∪ Ico 1003 1012 ∪ Ico 1013 1032',
                '{1063,1064,1095,2195,3296}) \\ {1}',
                '(2^67)^8807 - 1 - (∑ j ∈ support, (2^67)^j) - 2*(2^67)^1063'])
contains(high, ['def mu : ℕ := 2^51-2', 'def padding : ℕ := 2^65-1',
                'def lastPadding : ℕ := 2^19-1',
                '[4] ++ List.replicate 1012 0 ++ List.replicate 10 1 ++',
                'List.replicate 42 0 ++ List.replicate 9 1 ++',
                'List.replicate 1121 0 ++ [1] ++ List.replicate 1100 0 ++ [1] ++',
                'List.replicate 1096 0 ++ [mu] ++ List.replicate 1101 0 ++ [mu] ++',
                'List.replicate 3296 0 ++ List.replicate 13 padding ++ [lastPadding,0]'])
contains(ports, ['def lowNat : ℕ := Nat.ofDigits (2^67) (CompactListMask.digits (2^67) 8807 1063 CompactConcreteMask.support)',
                 'def highNat : ℕ := Nat.ofDigits (2^67) CompactHighPopulation.highDigits',
                 '![β,K,L,β+H]'])
source = json.loads((root / 'research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/probe.json').read_text())['source']
rows = {row[0]: row[1:] for row in source}
for name, definition in {'qm':['*','n_J','beta'], 'q':['+',1,'qm'], 'q2':['*','q','q'],
                         'g46':['-','q2',1], 'g47':['*','G','g46'], 'g48':['*','MF','q'],
                         'g49':['+','MC','g48'], 'g50':['*','n_J','g49'],
                         'R':['+','g47','g50']}.items():
    assert rows[name] == definition, (name, rows[name])

support = (set(range(943)) | set(range(983,993)) | set(range(1003,1012)) |
           set(range(1013,1032)) | {1063,1064,1095,2195,3296}) - {1}
mu, padding, last = 2**51-2, 2**65-1, 2**19-1
digits = ([4] + [0]*1012 + [1]*10 + [0]*42 + [1]*9 + [0]*1121 + [1] +
          [0]*1100 + [1] + [0]*1096 + [mu] + [0]*1101 + [mu] +
          [0]*3296 + [padding]*13 + [last,0])
assert len(digits) == 8807 and max(support) < 8807
rho = pow(2,67,3)
q = pow(rho,8807,3)
beta = (q-1) % 3
# Nat.ofDigits takes least-significant digit first.
high_horner = 0
for digit in reversed(digits):
    high_horner = (high_horner*rho + digit) % 3
high_sum = sum(d * pow(rho,i,3) for i,d in enumerate(digits)) % 3
assert high_horner == high_sum
low = (beta - sum(pow(rho,i,3) for i in support) - 2*pow(rho,1063,3)) % 3
low_digits = [(2**67-1 - (1 if i in support else 0) - (2 if i == 1063 else 0)) for i in range(8807)]
low_sum = sum(d*pow(rho,i,3) for i,d in enumerate(low_digits)) % 3
assert low == low_sum
mf = (beta + high_horner) % 3
rank = (low + q*mf) % 3
values = [(4*l*l+2*l-1) % 3 for l in range(3)]
assert (rho,q,beta,low,high_horner,mf,rank) == (2,2,1,1,0,1,0)
assert values == [2,2,1] and rank not in values
print(json.dumps({'N':67*8807, 'support_count':len(support),
 'support_even':sum(i%2==0 for i in support), 'support_odd':sum(i%2==1 for i in support),
 'modulus':3, 'rho':rho, 'q':q, 'beta':beta, 'MC':low, 'highNat':high_horner,
 'MF':mf, 'rank_J1':rank, 'power_match_values':values, 'solution_residues':[],
 'fixed_port_power_match_J1_impossible':True,
 'other_J_or_power_offsets_excluded':False, 'graph_nonexistence_proved':False,
 'large_values_expanded':False, 'lean_executed':False}, indent=2, sort_keys=True))
