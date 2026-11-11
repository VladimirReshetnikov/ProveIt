#!/usr/bin/env python3
"""Shifted-guard speculative graph and authenticated modular degree control; no Lean."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(p,h):
 raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h;return json.loads(raw)
c=load(H/'candidate.json','405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210')
p=load(D/'research/ordinary14-guarded-fold88-26/candidate.json','a3c5f7d9ed6f2c55a49818c5927f08b6293216bbecce24731a99890c83cc6ada')
assert c['witnesses']==p['witnesses'][:-1]+['omega'] and c['fixed_numerals']==p['fixed_numerals']
expect=[]
for row in p['source']:
 if row[0]=='g28':expect.append(['guard_base','-','g27','F'])
 elif row[0]=='Bt':continue
 elif row[0]=='bt_quotient':expect.append(['bt_quotient','*','qm','omega'])
 elif row[0]=='guard':expect.append(['guard','-','guard_base','bt_quotient'])
 else:expect.append(row)
assert c['source']==expect and len(c['source'])==87
assert len({row[0] for row in c['source']})==len(c['source'])
assert not ({row[0] for row in c['source']} & set(c['witnesses']+c['fixed_numerals']))
needed={'guarded_out'}
for n,op,x,y in reversed(c['source']):
 if n in needed:needed.update((x,y))
assert all(row[0] in needed for row in c['source']) and all(x in needed for x in c['witnesses']+c['fixed_numerals'])
# Bt is degree at most two; the added square cannot increase degree 26.
deg={x:1 for x in c['witnesses']};deg.update({x:0 for x in c['fixed_numerals']})
def dv(x):return 0 if isinstance(x,int) else deg[x]
for n,op,x,y in c['source']:deg[n]=dv(x)+dv(y) if op=='*' else max(dv(x),dv(y))
assert deg['guard']==2 and deg['guard2']==4
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf');b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']; z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')
assert fixed['beta']>0 and 0<=fixed['K0']<(fixed['beta']+1)**2
prime=1000000007
v={x:[0,1] for x in c['witnesses']};v.update({n:[x%prime] for n,x in fixed.items()})
def trim(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
def add(a,b,s):return trim([((a[i] if i<len(a) else 0)+s*(b[i] if i<len(b) else 0))%prime for i in range(max(len(a),len(b)))])
def mul(a,b):
 z=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):z[i+j]=(z[i+j]+x*y)%prime
 return trim(z)
def val(x):return [x%prime] if isinstance(x,int) else v[x]
for n,op,x,y in c['source']:v[n]=mul(val(x),val(y)) if op=='*' else add(val(x),val(y),1 if op=='+' else -1)
assert len(v['guarded_out'])-1==26 and v['guarded_out'][-1]!=0
print(json.dumps({'operations':87,'variables':14,'all_gates_inputs_ports_live':True,'K0_less_than_q_min_squared':True,'guard_degree_upper':4,'prime':prime,'ray_degree':26,'ray_leader':v['guarded_out'][-1],'scope':'external shifted-guard graph and finite degree controls; positive-zero equivalence unresolved; no Lean/PDF binding'},sort_keys=True,indent=2))
