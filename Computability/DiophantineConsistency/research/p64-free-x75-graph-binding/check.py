#!/usr/bin/env python3
"""Bind the symbolic full-zero formulas to the pinned free-X modified graph."""
import hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('Use python3 -I -S -B without optimization')
def require(b,s):
    if not b:raise RuntimeError(s)
base=Path(__file__).resolve().parent.parent
p=base/'p64-qcube76-independent-y-candidate'/'graph.json'
b=p.read_bytes(); sha=hashlib.sha256(b).hexdigest()
require(sha=='196ef3bdf6805c7ed7d44c278359e32c0f658634db357cc19f0e87464ed6b11c','76Y graph hash')
pins={
 'author/README.md':(base/'p64-free-x75-symbolic-full-zero'/'README.md','55b8461349833e654768451e4e1f1eba0862412c539b933e6282345ee622bbd1'),
 'author/check.py':(base/'p64-free-x75-symbolic-full-zero'/'check.py','ffb4100234a0ff058948198a307b2eb1f4b39bea35dea326bd048c4604f9c0ca'),
 'author/result.json':(base/'p64-free-x75-symbolic-full-zero'/'result.json','a61d203637a4b0eeebe25c9df3a91ab9fbeb2574beb8987e922d8acabc2b9c0f')}
for label,(path,expected_hash) in pins.items():
    require(hashlib.sha256(path.read_bytes()).hexdigest()==expected_hash,'witness pin '+label)
rows=json.loads(b)['source']
require(len(rows)==76 and len({r[0] for r in rows})==76,'76Y row count or duplicate')
require([r[0] for r in rows if 'X' in r[2:]]==['E','b0'],'X uses')
require([r[0] for r in rows if 'w' in r[2:]]==['X','Kplusw'],'w uses')
require([r[0] for r in rows if 'z' in r[2:]]==['transport_rhs'],'z uses')
require(['X','*','w','q'] in rows,'expected source X row')
rows=[[r[0],r[1],*['w' if x=='X' else x for x in r[2:]]] for r in rows if r[0]!='X']
expected='''
q_minus_one * beta J
q + q_minus_one 1
q2 * q q
q3 * q2 q
Y * q3 s
U * Y Y
E * w Y
k + eta zeta
kY * k Y
ell * E kY
ell_plus_k + ell k
first_product * ell ell_plus_k
first_unscaled_square * t t
A0 - first_unscaled_square first_product
c + kY eta
a + E Y
ac * a c
b0 + w ac
four_a * 4 a
H + four_a 3
a2 * a a
Delta + a2 H
c2 * c c
Delta_c2 * Delta c2
G + Delta_c2 1
q_minus_F - q F
C - q_minus_F alpha
gap_product * q_minus_one q_minus_F
gap + gap_product alpha
q2_minus_one - q2 1
R_product * gap q2_minus_one
qMF * q MF
mask_factor + MC qMF
mask * mask_factor J
R + R_product mask
r_plus_one - k R
r - r_plus_one 1
U_gamma * U gamma
main_gap - U_gamma r
H_main_gap * H main_gap
U_b0 * U b0
Dstar + U_b0 H_main_gap
Dstar2 * Dstar Dstar
U2 * U U
U2G * U2 G
M - Dstar2 U2G
Kplusw + K0 w
transport_product * Kplusw C
transport_sum - transport_product F
transport_rhs * z q_minus_one
Lt - transport_sum transport_rhs
f2 * f f
f2_minus_one - f2 1
cT * c T
quotient_gap - cT R
f2_quotient * f2 quotient_gap
V - f2_quotient c
V2 * V V
y2 * y y
square_gap - V2 y2
I * i c2
I2 * I I
Aaux * Delta f2_minus_one
W - I2 Aaux
aux_term * Aaux square_gap
Na + aux_term y2
unit_product * A0 Na
unit_minus_one - unit_product 1
unit_square * unit_minus_one unit_minus_one
M_square * M M
W_square * W W
Lt_square * Lt Lt
sum0 + unit_square M_square
sum1 + sum0 W_square
polynomial + sum1 Lt_square
'''
def parse(s):return int(s) if s.isdecimal() else s
expected_rows=[[parse(s) for s in line.split()] for line in expected.strip().splitlines()]
require(len(rows)==75 and rows==expected_rows,'75 source rows mismatch')
table={row[0]:row[1:] for row in rows}
# Independently named symbolic inputs and fixed ports.
inputs=set('J F alpha z f i T s w t eta zeta y gamma beta K0 MC MF'.split())
require(set(json.loads(b)['witnesses'])|set(json.loads(b)['fixed_numerals'])==inputs,'input names')
# Fully expand a gate to selected semantic cut points. +/* are flattened and
# sorted; this uses only associativity and commutativity, never a solver.
def val(x):return ('c',x) if isinstance(x,int) else ('v',x)
def op(s,*xs):
    if s in ('+','*'):
        ys=[]
        for x in xs:ys.extend(x[1:] if x[0]==s else [x])
        return (s,*sorted(ys,key=repr))
    require(s=='-' and len(xs)==2,'bad op')
    return (s,*xs)
def add(*xs):return op('+',*xs)
def mul(*xs):return op('*',*xs)
def sub(x,y):return op('-',x,y)
def sq(x):return mul(x,x)
def expand(name,stop):
    if isinstance(name,int):return val(name)
    if name in stop or name in inputs:return val(name)
    require(name in table,'unknown '+name)
    o,a,b=table[name]
    return op(o,expand(a,stop),expand(b,stop))
def check(name,stop,want):require(expand(name,set(stop.split()))==want,'formula mismatch '+name)
v=val
check('q_minus_one','',mul(v('beta'),v('J')))
check('q','q_minus_one',add(v('q_minus_one'),v(1)))
check('Y','q s',mul(sq(v('q')),v('q'),v('s')))
check('U','Y',sq(v('Y')))
check('E','w Y',mul(v('w'),v('Y')))
check('k','eta zeta',add(v('eta'),v('zeta')))
check('ell','w Y k',mul(v('w'),sq(v('Y')),v('k')))
check('A0','t ell k',sub(sq(v('t')),mul(v('ell'),add(v('ell'),v('k')))))
check('c','k Y eta',add(mul(v('k'),v('Y')),v('eta')))
check('a','w Y',add(mul(v('w'),v('Y')),v('Y')))
check('H','a',add(mul(v(4),v('a')),v(3)))
check('Delta','a H',add(sq(v('a')),v('H')))
check('R','q q_minus_one F alpha MC MF J',add(mul(add(mul(v('q_minus_one'),sub(v('q'),v('F'))),v('alpha')),sub(sq(v('q')),v(1))),mul(add(v('MC'),mul(v('q'),v('MF'))),v('J'))))
check('Dstar','U w a c H gamma k R',add(mul(v('U'),add(v('w'),mul(v('a'),v('c')))),mul(v('H'),sub(mul(v('U'),v('gamma')),sub(sub(v('k'),v('R')),v(1))))))
check('M','Dstar U Delta c',sub(sq(v('Dstar')),mul(sq(v('U')),add(mul(v('Delta'),sq(v('c'))),v(1)))))
check('Lt','K0 w q F alpha z q_minus_one',sub(sub(mul(add(v('K0'),v('w')),sub(sub(v('q'),v('F')),v('alpha'))),v('F')),mul(v('z'),v('q_minus_one'))))
check('I','i c',mul(v('i'),sq(v('c'))))
check('W','I Delta f',sub(sq(v('I')),mul(v('Delta'),sub(sq(v('f')),v(1)))))
check('V','f c T R',sub(mul(sq(v('f')),sub(mul(v('c'),v('T')),v('R'))),v('c')))
check('Na','Delta f V y',add(mul(v('Delta'),sub(sq(v('f')),v(1)),sub(sq(v('V')),sq(v('y')))),sq(v('y'))))
check('polynomial','A0 Na M W Lt',add(sq(sub(mul(v('A0'),v('Na')),v(1))),sq(v('M')),sq(v('W')),sq(v('Lt'))))
# Separate exact polynomial check for the forward transport map.
# Variables q,w,z,C,F,K represent arbitrary ring elements. The positivity of C
# on a positive old zero is explained in README and is not a polynomial fact.
def plus(a,b):
    r=dict(a)
    for mono,coef in b.items():r[mono]=r.get(mono,0)+coef
    return {mono:coef for mono,coef in r.items() if coef}
def neg(a):return {m:-c for m,c in a.items()}
def minus(a,b):return plus(a,neg(b))
def prod(a,b):
    r={}
    for ma,ca in a.items():
        for mb,cb in b.items():
            mono=tuple(sorted(ma+mb));r[mono]=r.get(mono,0)+ca*cb
    return {mono:coef for mono,coef in r.items() if coef}
def var(x):return {(x,):1}
one={():1}; q,w,z,C,F,K=map(var,('q','w','z','C','F','K'))
old=minus(minus(prod(plus(K,w),C),F),prod(z,minus(q,one)))
wnew=prod(q,w);znew=plus(z,prod(w,C))
new=minus(minus(prod(plus(K,wnew),C),F),prod(znew,minus(q,one)))
require(old==new,'forward transport identity')
wrong=minus(minus(prod(plus(K,wnew),C),F),prod(minus(z,prod(w,C)),minus(q,one)))
require(old!=wrong,'negative-control transport identity')
# Every retained gate is live in the final polynomial.
live=set();stack=['polynomial']
while stack:
    name=stack.pop()
    if name in live or name not in table:continue
    live.add(name)
    stack.extend(x for x in table[name][1:] if isinstance(x,str))
require(live==set(table),'dead retained gate')
raw=json.dumps(rows,separators=(',',':')).encode()
result={'status':'PASS_PINNED_GRAPH_BINDING','script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        'source_graph_sha256':sha,'free_x_graph_sha256_canonical_json':hashlib.sha256(raw).hexdigest(),
        'source_rows':76,'X_uses':['E','b0'],'modified_rows':75,'live_modified_rows':len(live),
        'author_sha256':{label:h for label,(_,h) in pins.items()},
        'checked_symbolic_formulas':21,'forward_transport_identity':True,'wrong_sign_negative_control':True,
        'scope':'Structural row and expression binding to the symbolic zero proof; no Lean theorem and no independent verification of its arithmetic proof.'}
print(json.dumps(result,indent=2,sort_keys=True))
