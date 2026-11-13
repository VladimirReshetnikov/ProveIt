#!/usr/bin/env python3
"""Independent exact witness evaluation and graph edit check; no Lean."""
import hashlib,json,operator,zlib
from pathlib import Path
D=Path(__file__).resolve().parents[2]
def sha(b): return hashlib.sha256(b).hexdigest()
def load(p,h):
 d=(D/p).read_bytes();assert sha(d)==h,p;return json.loads(d)
p=load('research/ordinary14-natural-forcedj81/candidate.json','24d0c9f0f7d0078f268b27f6d3a0698952fbc0b13c4d28b4e5f9152dc4a41999')
c=load('research/ordinary14-natural80-unshift-s-obstruction/candidate.json','bbdd14c8bb424a65803d3624d404ba17cdad1cb053cc38401218c22be2780559')
assert p['witnesses']==c['witnesses'] and p['domain']==c['domain']=='nonnegative integers'
assert p['fixed_numerals']==c['fixed_numerals']==['beta','K0','MC','MF']
old={r[0]:r[1:] for r in p['source']};new={r[0]:r[1:] for r in c['source']}
assert len(old)==81 and len(new)==80 and set(old)-set(new)=={'s'} and set(new)<=set(old)
assert old['s']==['+','n_s',1]
for name,row in new.items():
 op,x,y=old[name];assert row==[op,'n_s' if x=='s' else x,'n_s' if y=='s' else y]
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def eval_graph(graph,env):
 v=env.copy()
 for name,op,x,y in graph['source']:
  assert name not in v
  a=x if type(x) is int else v[x];b=y if type(y) is int else v[y]
  v[name]=ops[op](a,b)
 return v

def example(ports):
 beta,K0,MC,MF=(ports[n] for n in ('beta','K0','MC','MF'))
 assert beta>=2 and K0>=0 and MC>0 and MF>0
 w=(1-K0)%beta
 if w==0:w=beta
 q=beta+1
 R=(beta*beta+beta-1)*(q*q-1)+MC+MF*q
 assert w>0 and R>0 and (q*w+K0-1)%beta==0
 h=(q*w+K0-1)//beta
 ordinary={'J':1,'F':1,'alpha':beta-1,'f':2,'i':3,'T':R,'w':w,'s':0,'r':1,'eta':1,'zeta':R,'y':1,'gamma':1,'h':h}
 direct={'J','f','s','r','y','h'}
 v={'n_'+n:(x if n in direct else x-1) for n,x in ordinary.items()}
 assert set(v)==set(c['witnesses']) and all(x>=0 for x in v.values())
 v.update(ports); out=eval_graph(c,v)
 expected={'q':q,'X':q*w,'Y':0,'U':0,'ell':0,'c':1,'k':R+1,'R':R,'Dstar':0,'Q':9,'V':-1,'F0':1,'F1':1,'Fa':1,'Fs':1,'guard':1,'out':0}
 for n,x in expected.items(): assert out[n]==x,(n,out[n],x)
 return v

toy={'beta':2,'K0':1,'MC':1,'MF':1}
v=example(toy)
assert tuple(v[n] for n in c['witnesses'])==(1,0,0,2,2,43,1,0,1,0,43,1,0,3)
parent_out=eval_graph(p,v)['out'];assert parent_out!=0
root='con-zfc-diophantine-forms/72-congruence-sextic/positive13/'
a=load(root+'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,m in a['ports'].items():
 assert all(m[k]==b['ports'][n][k] for k in ('sha256_raw','sha256_gzip','raw_bytes','bits'))
 packed=(D/root/m['path']).read_bytes();raw=zlib.decompress(packed,31)
 assert sha(packed)==m['sha256_gzip'] and sha(raw)==m['sha256_raw'] and len(raw)==m['raw_bytes']
 ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==m['bits']
assert set(ports)=={'beta','K0','MC','MF'}
example(ports)
print(json.dumps({'scope':'exact toy and authenticated port counterexamples to forced s positivity; not an existence-inequivalence proof',
 'candidate_gates':80,'parent_gates':81,'toy_parent_nonzero':True,'authenticated_zero':True,
 'all_factor_units_checked':True,'ports_reauthenticated':len(ports)},sort_keys=True,indent=2))
