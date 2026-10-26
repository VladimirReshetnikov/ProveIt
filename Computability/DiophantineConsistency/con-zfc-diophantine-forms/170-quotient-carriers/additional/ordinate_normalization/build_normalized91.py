#!/usr/bin/env python3
"""Build the ordinary universal 91-operation ordinate-residue chart.

This is an auxiliary research artifact, not the fixed Con(ZFC) endpoint.
The semantic proof uses the named complete84 parent and canonical completion.
"""
from pathlib import Path
import json
from collections import Counter

ROOT = Path(__file__).resolve().parent
parent = json.loads((ROOT / 'parent84.json').read_text())['packet']
depends = {'f', 'y_aux'}
source = []
for row in parent['source']:
    name, op, left, right = row
    if left in depends or right in depends:
        depends.add(name)
    else:
        source.append(row)
if len(source) != 66:
    raise ValueError(('Unexpected retained producer count', len(source)))

# These names have distinct meanings from retained source A (= Delta).
tail = [
    ['nr_I', '*', 'i', 'c2'],
    ['nr_Dminus1', '*', 'nr_I', 'aux_coefficient_root'],
    ['nr_D', '+', 'nr_Dminus1', 1],
    ['nr_RD', '*', 'r_lhs', 'nr_D'],
    ['nr_b', '+', 'R10a', 'nr_RD'],
    ['nr_u', '*', 'R10a', 'auxiliary_quotient'],
    ['nr_u2', '*', 'nr_u', 'nr_u'],
    ['nr_p', '*', 'nr_D', 'nr_u2'],
    ['nr_b2', '*', 'nr_b', 'nr_b'],
    ['nr_P5a', '*', 'norm_triple', 'norm_index'],
    ['nr_P5', '*', 'nr_P5a', 'norm_transport'],
    ['nr_Qz', '*', 'R16', 'ordinate_quotient'],
    ['nr_Qzmz', '-', 'nr_Qz', 'ordinate_quotient'],
    ['nr_Qzm2', '-', 'nr_Qz', 2],
    ['nr_Wminus1', '*', 'nr_Qzmz', 'nr_Qzm2'],
    ['nr_sum', '+', 'nr_p', 'nr_b2'],
    ['nr_Aplus1', '-', 'nr_sum', 'nr_Wminus1'],
    ['nr_A', '-', 'nr_Aplus1', 1],
    ['nr_cross', '*', 'nr_p', 'nr_b2'],
    ['nr_four', '*', 4, 'nr_cross'],
    ['nr_A2', '*', 'nr_A', 'nr_A'],
    ['nr_K', '-', 'nr_A2', 'nr_four'],
    ['nr_unit', '+', 'nr_K', 1],
    ['nr_product', '*', 'nr_P5', 'nr_unit'],
    ['polynomial91', '-', 'nr_product', 1],
]
source += tail
witnesses = [x for x in parent['witnesses'] if x != 'f']
witnesses[witnesses.index('y_aux')] = 'ordinate_quotient'
packet = {
    'name': 'universal17_normalized_ordinate91',
    'domain': 'strictly positive integers',
    'ordinary_input': parent['ordinary_input'],
    'fixed_numerals': parent['fixed_numerals'],
    'witnesses': witnesses,
    'free': witnesses + [parent['ordinary_input']] + parent['fixed_numerals'],
    'source': source,
    'output': 'polynomial91',
    'operations': len(source),
    'operation_counts': dict(Counter(r[1] for r in source)),
    'exact_degree': 269,
    'uniform_leader': '-32*h*(rho+sigma)*delta^2*i^8*(eta+zeta)^19*w^26*s^45*(Bm1*Jrep)^161*Ttransport*ordinate_quotient^4',
    'nonzero_coefficient': '32*Bm1^162',
    'nonzero_monomial': 'Jrep^162*h*rho*delta^2*i^8*eta^19*w^26*s^45*transport_quotient*ordinate_quotient^4',
    'projection': 'y_aux=R16*ordinate_quotient-1; f=nr_A/(2*nr_u*nr_b)',
    'zero_set_claim': 'Positive new zeros restore unique positive parent roots; canonical parent completions lie in this residue chart. Existence equivalence is asserted, not surjectivity onto all parent zero tuples.',
    'scope': 'Auxiliary universal construction; not a new fixed Con(ZFC) Pareto record.',
    'proof': 'NORMALIZED_ORDINATE_PROOF.md',
}
if len(witnesses) != 17 or len(source) != 91:
    raise ValueError('Wrong endpoint size')
defined = set(packet['free'])
for name,op,left,right in source:
    if name in defined or op not in {'+','-','*'}:
        raise ValueError('Malformed producer')
    for operand in (left,right):
        if not isinstance(operand,int) and operand not in defined:
            raise ValueError(('Missing producer',operand))
    defined.add(name)
live = {packet['output']}
for name,op,left,right in reversed(source):
    if name in live:
        if isinstance(left,str): live.add(left)
        if isinstance(right,str): live.add(right)
if not all(r[0] in live for r in source) or not all(v in live for v in packet['free']):
    raise ValueError('Dead row or input')
(ROOT/'equation91_degree269.json').write_text(json.dumps(packet,indent=2)+'\n')
print(json.dumps({k:packet[k] for k in ['operations','operation_counts','exact_degree']}))
