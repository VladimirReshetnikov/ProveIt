#!/usr/bin/env python3
"""Check the finite algebra underlying a symbolic enormous positive zero.

The gigantic Pell power itself is *not expanded*. Its integrality and Pell
identity follow by the binomial argument documented in README.md.
"""
from pathlib import Path
import hashlib
import json

if not __debug__:
    raise RuntimeError('optimized Python is unsupported')
root = Path(__file__).resolve().parent.parent
old_paths = [
    ('adaptive-square-sums/candidate.json', '11fb3c192fb3a8ab9204ef0a5401198d986e002242e4f48442147aa356263828'),
    ('adaptive-direct-ordinate86/candidate.json', 'e9889a81a491b85491dde749e82158109ea98ff94ed41fc0f05dc810ec58b91f'),
]
for rel, pin in old_paths:
    data = (root / rel).read_bytes()
    assert hashlib.sha256(data).hexdigest() == pin
    graph = json.loads(data)
    rows = {x[0]: x for x in graph['source']}
    expected = [
        ['q', '+', 1, 'qm'], ['qm', '*', 'J', 'beta'],
        ['qF', '-', 'q', 'F'], ['C', '-', 'qF', 'alpha'],
        ['q2', '*', 'q', 'q'], ['q3', '*', 'q', 'q2'],
        ['U', '*', 'Y', 'q2'], ['M', '*', 'q3', 'qm'],
        ['E', '*', 'X', 'Y'], ['k', '+', 'eta', 'zeta'],
        ['kY', '*', 'Y', 'k'], ['c', '+', 'eta', 'kY'],
        ['c2', '*', 'c', 'c'], ['a', '+', 'E', 'Y'],
        ['H', '+', 3, 'g15'], ['g15', '*', 4, 'a'],
        ['Delta', '+', 'H', 'g17'], ['g17', '*', 'a', 'a'],
        ['b0', '+', 'X', 'g19'], ['g19', '*', 'a', 'c'],
        ['g25', '*', 'K0', 'q'], ['g26', '+', 'X', 'g25'],
        ['g27', '*', 'C', 'g26'], ['g28', '*', 'F', 'q'],
        ['Bt', '-', 'g27', 'g28'], ['Z', '-', 'root_sum', 'root_btq3'],
        ['root_sum', '+', 'root_scaled', 'g33'], ['root_scaled', '*', 'M', 'root_inner'],
        ['g33', '*', 'Y', 'qm'], ['root_btq3', '*', 'Bt', 'q3'],
        ['g38', '*', 'Z', 'Z'], ['g39', '*', 'M', 'M'],
        ['g42', '*', 'g39', 'g41'], ['A0', '-', 'g38', 'g42'],
        ['g46', '-', 'q2', 1], ['g47', '*', 'G', 'g46'],
        ['g48', '*', 'MF', 'q'], ['g49', '+', 'MC', 'g48'],
        ['g50', '*', 'J', 'g49'], ['R', '+', 'g47', 'g50'],
        ['g52', '-', 'k', 'R'], ['r0', '-', 'g52', 1],
        ['g54', '*', 'U', 'gamma'], ['g55', '*', 'E', 'q'],
        ['g56', '+', 'g54', 'g55'], ['shift', '-', 'g56', 'r0'],
        ['g58', '*', 'U', 'b0'], ['g59', '*', 'H', 'shift'],
        ['Dstar', '+', 'g58', 'g59'], ['g61', '*', 'Dstar', 'Dstar'],
        ['g62', '*', 'U', 'U'], ['g63', '*', 'Delta', 'c2'],
        ['g64', '+', 1, 'g63'], ['g65', '*', 'g62', 'g64'],
        ['A1', '-', 'g61', 'g65'], ['f2', '*', 'f', 'f'],
        ['rho', '-', 'f2', 1], ['Q', '*', 'Delta', 'rho'],
        ['I', '*', 'c2', 'i'], ['g71', '*', 'I', 'I'],
        ['g72', '-', 'g71', 'Q'], ['g74', '*', 'T', 'c'],
        ['g75', '-', 'g74', 'R'], ['g76', '*', 'f2', 'g75'],
        ['V', '-', 'g76', 'c'], ['y2', '*', 'y', 'y'],
        ['g80', '*', 'V', 'V'], ['g81', '-', 'y2', 'g80'],
        ['g82', '*', 'Q', 'g81'], ['Fa', '-', 'y2', 'g82'],
    ]
    assert all(rows[row[0]] == row for row in expected)
    if graph['output'] == 'sumSquares':
        for row in [
            ['auxResidual','-','Fa',1], ['firstSquare','*','A0','A0'],
            ['mainSquare','*','A1','A1'], ['auxSquare','*','auxResidual','auxResidual'],
            ['strongSquare','*','g72','g72'], ['firstMain','+','firstSquare','mainSquare'],
            ['firstMainAux','+','firstMain','auxSquare'],
            ['sumSquares','+','firstMainAux','strongSquare'],
        ]:
            assert rows[row[0]] == row
    else:
        assert graph['output'] == 'P13'
        for row in [
            ['F0','+',1,'A0'], ['F1','+',1,'A1'], ['Fs','+',1,'g72'],
            ['g86','*','F0','F1'], ['g87','*','Fa','g86'],
            ['g88','*','Fs','g87'], ['P13','-','g88',1],
        ]:
            assert rows[row[0]] == row

# Pell (s+c*sqrt(15))=(4+sqrt(15))^15. Only these small constants are expanded.
s, c = 1, 0
for _ in range(15):
    s, c = 4*s + 15*c, s + 4*c
assert (s, c) == (13837575261124, 3572846569215)
assert s*s - 15*c*c == 1 and c % 2 == 1
# Compute only the Pell coefficient modulo c^2, by binary exponentiation;
# the actual enormous f and B are never expanded.
def pell_mul(x,y,modulus):
    return ((x[0]*y[0]+15*x[1]*y[1]) % modulus,
            (x[0]*y[1]+x[1]*y[0]) % modulus)
def pell_power(base,exponent,modulus):
    result=(1,0)
    while exponent:
        if exponent & 1: result=pell_mul(result,base,modulus)
        base=pell_mul(base,base,modulus)
        exponent//=2
    return result
reduced_f,reduced_B = pell_power((s,c),c,c*c)
assert reduced_B == 0 and (reduced_f*reduced_f-15*reduced_B*reduced_B) % (c*c) == 1
k = c - 1
eta, zeta = 1, c - 2
assert eta > 0 and zeta > 0 and eta + zeta == k and eta + k == c
b0 = 1 + 2*c
assert (-s-b0) % 11 == 0
R0 = (-s-b0)//11 + k - 2
assert R0 == 1665276714707 and R0 > 0
assert b0 + 11*(R0 + 2 - k) == -s
assert s*s == 1 + 15*c*c

# Polynomial arithmetic in Z[t]; t=I^2. Auxiliary Pell's odd exponent 15.
def add(a,b,sgn=1):
    out=a.copy()
    for i,v in b.items(): out[i]=out.get(i,0)+sgn*v
    return {i:v for i,v in out.items() if v}
def mul(a,b):
    out={}
    for i,x in a.items():
        for j,y in b.items(): out[i+j]=out.get(i+j,0)+x*y
    return {i:v for i,v in out.items() if v}
T={1:1}; one={0:1}; factor={1:4,0:-2}
v0,v1=one,{1:4,0:-3}
y0,y1=one,{1:4,0:-1}
for _ in range(1,7):
    v0,v1=v1,add(mul(factor,v1),v0,-1)
    y0,y1=y1,add(mul(factor,y1),y0,-1)
V,Y=v1,y1
assert add(mul(T,mul(V,V)),mul(add(T,one,-1),mul(Y,Y)),-1)==one
assert add(mul(T,mul(V,V)),mul(add(T,one,-1),mul(Y,Y))) != one
assert sum(coeff*(-15)**deg for deg,coeff in V.items()) == -c
# Thus V(t)+c is divisible by t+15=15*f^2 whenever t=15*(f^2-1).
assert 225**6 > c
# For t>=225, v_j increases and v_j>=t^j; f^2 <= t. Hence
# P=(V(t)+c)/f^2 >= t^7/f^2 >= t^6 > c. This is a proof
# by the displayed recurrence, not evaluation of the enormous Pell power.
print('PASS_SYMBOLIC_AUXILIARY_PORT_COUNTEREXAMPLE',
      json.dumps({'c':c,'s':s,'R0':R0,'q':1,'h':2,'C':1,
                  'v_minus_15':-c,'auxiliary_pell_exponent':15,
                  'scope':'beta=0; auxiliary signed integer ports; symbolic Pell power not expanded'},sort_keys=True))
