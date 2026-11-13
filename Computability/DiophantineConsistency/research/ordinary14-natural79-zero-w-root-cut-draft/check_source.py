#!/usr/bin/env python3
"""Bounded literal-root source, AST, and finite controls; no Lean."""
import hashlib,json,random
from pathlib import Path
P=Path(__file__).resolve().parent;D=P.parents[1]
files={
 'draft':(P/'Natural79ZeroWRootCut.lean','c3fd2660899139ddd335214893e5698a4124399432604111a6aa1942bc8009ec'),
 'norm':(D/'research/ordinary14-natural79-zero-w-main-norm-draft/Natural79ZeroWMainNorm.lean','afacf4636f4b66e2bff939300347ba5568b72d477a3028ec0a424aba42ce8009'),
 'atoms':(D/'research/ordinary14-natural79-factor-residues-draft/Natural79ResidueShapes.lean','b4d60c7db8fb92cac53f38f81414a6319d8979ccbcb575d2e29e49fa5a51fd38'),
 'ring_divisibility':(D/'research/ordinary14-natural79-w-model-route/ForcedWDivisibility.lean','111f5a6da543baf6f08b3b1c6e5e8371cfb222197ba4566b8693598edffb6833'),
 'json':(D/'research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'),
}
s={}
for name,(path,want) in files.items():
 data=path.read_bytes(); assert hashlib.sha256(data).hexdigest()==want,name;s[name]=data.decode()
for needle in ('theorem root_expr_shape','theorem root_eval_zero_w','theorem represented_root_zero_w',
  'theorem divisor_of_root_cut','theorem signed_dvd_three_square_of_zero_w_zero',
  'signed_quotient_of_zero_w_zero p beta v hbeta hb hJ hz hw',
  'divisor_of_main_norm H U d Y C hd hn','divisor_of_three_square H U Q Y rfl hU hHU'):
 assert needle in s['draft'],needle
for needle in ('theorem atoms_at_zero_w','theorem signed_quotient_of_zero_w_zero','d*d=ι (normRhs beta v)'):
 assert needle in s['norm'],needle
for needle in ('theorem divisor_of_main_norm','theorem divisor_of_three_square'):
 assert needle in s['ring_divisibility'],needle
assert 'sorry' not in s['draft'] and 'admit' not in s['draft']
# Compare unexpanded literal expression trees with the documented exact root cut.
a=json.loads(s['json']); e={n:('var',n) for n in a['witnesses']};e.update({n:('port',n) for n in a['fixed_numerals']})
def val(x):return ('num',x) if type(x) is int else e[x]
for n,op,x,y in a['source']: e[n]=(op,val(x),val(y))
def add(x,y):return ('+',x,y)
def sub(x,y):return ('-',x,y)
def mul(x,y):return ('*',x,y)
one=('num',1);three=('num',3);four=('num',4)
q=add(one,mul(e['n_J'],e['beta'])); assert e['q']==q
X=mul(q,e['n_w']); assert e['X']==X
shift=sub(mul(e['U'],e['n_gamma']),sub(add(add(e['n_eta'],one),e['n_zeta']),e['R']))
assert e['shift']==shift
assert e['Dstar']==add(mul(e['U'],add(X,mul(e['a'],e['c']))),mul(add(three,mul(four,e['a'])),shift))
assert e['a']==add(mul(X,e['Y']),e['Y']) and e['U']==mul(e['Y'],mul(q,q))
# Finite arbitrary-port controls confirm the zero-w specializing equation.
rng=random.Random(790721);prime=1000003
for _ in range(300):
 env={n:rng.randrange(-7,8)%prime for n in a['witnesses']+a['fixed_numerals']};env['n_w']=0
 def evaluate(x):return x%prime if type(x) is int else env[x]
 for n,op,x,y in a['source']:
  x,y=evaluate(x),evaluate(y);env[n]=(x+y if op=='+' else x-y if op=='-' else x*y)%prime
 assert env['a']==env['Y']
 assert env['Dstar']==(env['U']*env['Y']*env['c']+(4*env['Y']+3)*env['shift'])%prime
 assert env['U']==env['Y']*env['q']**2%prime
print(json.dumps({'scope':'source signatures, literal graph AST and finite controls; no Lean/model/iPRA proof',
 'pinned_files':len(files),'exact_literal_AST_cuts':5,'arbitrary_port_w_zero_controls':300,
 'main_norm_and_signed_quotient_are_unelaborated_inputs':True,'ring_divisibility_lemmas_are_unelaborated_inputs':True},sort_keys=True,indent=2))
