#!/usr/bin/env python3
"""Independent complete expansion, scale maps and beta-source audit."""
from pathlib import Path
import collections,hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
p=json.loads(pin('research/adaptive-aq22-two-quotients110/candidate.json','b82ef3f8e45cc260d8ffee26f3f8fa7ef2f207834829aee1a5ac357fcab0ffc1'))
c=json.loads(pin('research/adaptive-aq20-substituted-scales104/candidate.json','e21601ed2d0a17aa72ad1bbe103122337ecf98455cf39d9e97a22883d1c9ab50'))
n=json.loads(pin('research/adaptive-aq20-substituted-scales104/natural-candidate.json','f24f0d1adefd50c3ebe93cc0f4d1289f84e47e3ce479e88e5c9db4fdaef1485f'))
pin('research/adaptive-aq20-substituted-scales104/receipt.json','792bd8e4a41b11c025d5cc8ed29a22608caed337c212414a305f64eca1423eb6')
m=pin('Lean/DiophantineConsistency/ModelThirteenCarrier.lean','57f3cf755891aa921e9d97877af373e9194c6aa709a259c47678e4a370fd0185')
bp=pin('Lean/DiophantineConsistency/ModelCarrierCurrent.lean','f0a4898f545a932b135783799ae0d44179fbcbcb08e5d97eaced4515740e990f')
pin('Lean/DiophantineConsistency/CurrentMaskData2011.lean','8e92c1f507bc250c31fb2671a921dfbef7a44ba643956f962cd64d9b50bd4582')
pin('Lean/DiophantineConsistency/CurrentMasks2011.lean','403f35c26ffd2d94e4a29af8c826cfa0874ac8f2281bb673c1347989e7d48cea')
assert 'theorem port0 : (ringPorts (V := V)) 0 = ι (CurrentMasks2011.beta : V)' in m
assert 'theorem beta_pos : (0 : DiffRing V) < ((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V)' in bp
assert len(p['witnesses'])==22 and len(c['witnesses'])==len(n['witnesses'])==20 and len(p['source'])==110 and len(c['source'])==104 and len(n['source'])==124
assert c['witnesses']==[x for x in p['witnesses'] if x not in ('scaleVariable','mainScaleVariable')]
ren={x:'n_'+x for x in c['witnesses']};rep=lambda x:'shift_'+x if isinstance(x,str) and x in ren else x
assert n['witnesses']==list(ren.values()) and n['source']==[['shift_'+x,'+',ren[x],1] for x in c['witnesses']]+[[x,op,rep(a),rep(b)] for x,op,a,b in c['source']]
assert n['fixed_numerals']==c['fixed_numerals'] and n['output']==c['output']
def atom(x):return {(x,):1}
def add(a,b,k=1):
 d=dict(a)
 for m,v in b.items():d[m]=d.get(m,0)+k*v
 return {m:v for m,v in d.items() if v}
def mul(a,b):
 d=collections.defaultdict(int)
 for ma,ca in a.items():
  for mb,cb in b.items():d[tuple(sorted(ma+mb))]+=ca*cb
 return {m:v for m,v in d.items() if v}
def run(g,subs):
 env={x:atom(x) for x in g['witnesses']+g['fixed_numerals']};env.update(subs);rows={}
 for name,op,a,b in g['source']:
  assert name not in env and op in '+-*';rows[name]=(a,b)
  a=env[a] if isinstance(a,str) else ({():a} if a else {})
  b=env[b] if isinstance(b,str) else ({():b} if b else {})
  env[name]=mul(a,b) if op=='*' else add(a,b,-1 if op=='-' else 1)
 active={g['output']};todo=[g['output']]
 while todo:
  for x in rows.get(todo.pop(),()):
   if isinstance(x,str) and x not in active:active.add(x);todo.append(x)
 assert set(rows)|set(g['witnesses'])|set(g['fixed_numerals'])<=active
 return env
b=run(c,{})
qm=mul(atom('J'),atom('beta'));qq=add({():1},qm);q2=mul(qq,qq);q3=mul(q2,qq)
M=mul(q3,qm);U=mul(atom('Y'),q2)
assert b['M']==M and b['U']==U
# Every output term is independently expanded over all inputs and ports.
a=run(p,{'scaleVariable':M,'mainScaleVariable':U})
assert a[p['output']]==b[c['output']] and not a['scaleDifference'] and not a['mainScaleDifference']
inputs=set(c['witnesses']);out=b[c['output']];degree=lambda mon:sum(x in inputs for x in mon)
assert max(map(degree,out))==14
witness=tuple(sorted(['J']*10+['X']*2+['eta']*2))
coeff={tuple(x for x in mon if x not in inputs):v for mon,v in out.items() if tuple(x for x in mon if x in inputs)==witness}
assert coeff and all(set(mon)<= {'beta'} for mon in coeff)
assert len(coeff)==1 and next(iter(coeff))==('beta',)*10 and next(iter(coeff.values()))>0
zero_beta={mon:k for mon,k in out.items() if 'beta' not in mon}
print(json.dumps({'scope':'full symbolic output identity and pinned beta model sources; no Lean','positive_variables':20,'positive_operations':104,'natural_operations':124,'output_terms':len(out),'degree_at_nonzero_beta':14,'degree_at_beta_zero':max(map(degree,zero_beta)),'degree14_witness_beta_power':10,'degree14_witness_coefficient':next(iter(coeff.values())),'model_beta_representation_source':True,'model_beta_strict_positivity_source':True,'new_model_transport_not_elaborated':True},sort_keys=True,indent=2))
