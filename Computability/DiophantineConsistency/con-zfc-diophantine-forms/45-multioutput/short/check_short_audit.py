"""Authored finite checks; upstream files are parsed as data, never executed."""
import json
from pathlib import Path
import sympy as S

ROOT = Path(__file__).resolve().parent

def require(p, message):
    if not p:
        raise RuntimeError(message)

for filename, count in [('product67.json', 67), ('retained16_system59.json', 59)]:
    packet = json.loads((ROOT / 'upstream' / filename).read_text())
    source = packet['source']
    require(len(source) == count, 'Wrong gate count: ' + filename)
    inputs = set(packet['witnesses'] + packet['fixed_numerals'])
    known = inputs.copy()
    for name, op, a, b in source:
        require(op in ('+', '-', '*'), 'Nonbinary arithmetic gate')
        require(name not in known, 'Duplicate output')
        require(all(isinstance(x, int) or x in known for x in (a, b)), 'Forward reference')
        known.add(name)
    if 'output' in packet:
        live = {packet['output']}
    else:
        live = {x for pair in packet['comparisons'] for x in pair if isinstance(x, str)}
    needed = set()
    for name, op, a, b in reversed(source):
        if name in live:
            needed.add(name)
            live.update(x for x in (a, b) if isinstance(x, str))
    require(len(needed) == count, 'Dead gate')
    require(inputs <= live, 'Dead input')

beta,J,G,MC,MF,L,r,k,a,c,H,X,gamma,V,I = S.symbols('beta J G MC MF L r k a c H X gamma V I')
q = beta*J+1
B = X+gamma*H
identities = [
    G*(q*q-1)+(MC+q*MF)*J-J*(beta*G*(q+1)+MC+q*MF),
    (L+r)**2-L*(L+k)-(r*r+L*(2*r-k)),
    (a*c+B)**2-(a*a+H)*c*c-(B*(B+2*a*c)-H*c*c),
    I*I*(V*V-(V+r)**2)+(V+r)**2-((V+r)**2-I*I*r*(2*V+r)),
]
for expression in identities:
    require(S.expand(expression) == 0, 'Identity failed')
require(8*1**2-2**2 == 4 and 8 % 4 == 0, 'Proper-divisor example')
print('PASS: two exact ledgers and live input/gate audits; four polynomial identities; proper-divisor cancellation obstruction.')
