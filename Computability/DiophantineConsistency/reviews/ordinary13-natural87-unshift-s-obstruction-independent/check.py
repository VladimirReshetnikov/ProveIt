#!/usr/bin/env python3
"""Independent graph, port and concrete-witness checks; no Lean execution."""
from pathlib import Path
import hashlib,json,operator,zlib
D=Path(__file__).resolve().parents[2]
def digest(b):return hashlib.sha256(b).hexdigest()
def read(path,h):
 data=path.read_bytes();assert digest(data)==h,str(path);return json.loads(data)
old=read(D/'research/ordinary13-natural-unit-product88/candidate.json','95fdd3495b777a0bdf64c95f6dd24cda660dee42f0508c76fdb081da21f42a5a')
new=read(D/'research/ordinary13-natural87-unshift-s-obstruction/candidate.json','6de3dc2c7309255848a82ef35e161bbd5961fdc35bb9f0b232c694ce6e7a69a8')
oldrows={r[0]:r[1:] for r in old['source']};newrows={r[0]:r[1:] for r in new['source']}
assert len(oldrows)==88 and len(newrows)==87 and oldrows['s']==['+','n_s',1]
assert set(oldrows)-set(newrows)=={'s'} and not (set(newrows)-set(oldrows))
for name,row in newrows.items():
 op,x,y=oldrows[name]
 assert row==[op, 'n_s' if x=='s' else x, 'n_s' if y=='s' else y],name
assert old['witnesses']==new['witnesses'] and old['fixed_numerals']==new['fixed_numerals']
assert new['domain']==old['domain']=='nonnegative integers'
known=set(new['witnesses']+new['fixed_numerals']);assert len(known)==17 and len(new['witnesses'])==13
for n,op,x,y in new['source']:
 assert n not in known and op in ('+','-','*') and all(isinstance(v,int) or v in known for v in (x,y))
 known.add(n)
live={new['output']}
for n,op,x,y in reversed(new['source']):
 if n in live:live.update(v for v in (x,y) if isinstance(v,str))
assert all(n in live for n,*_ in new['source']) and set(new['witnesses']+new['fixed_numerals'])<=live
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evaluate(graph, inputs):
 env=inputs.copy()
 for n,op,x,y in graph['source']:
  env[n]=ops[op](env[x] if isinstance(x,str) else x,env[y] if isinstance(y,str) else y)
 return env
# Use division with remainder rather than the candidate checker's compact
# expression to construct the same family from independently computed data.
def check(beta,K0,MC,MF):
 assert beta>=2 and K0>=0 and MC>0 and MF>0
 _,w=divmod(1-K0,beta)
 if w==0:w=beta
 q=beta+1; rank=(beta-1+beta*beta)*(q*q-1)+MC+MF*q
 B=q*w+K0-1;t,rem=divmod(B,beta)
 assert w>0 and rank>0 and B>0 and rem==0 and t>0
 k=rank+1;r=k*B+t-k+1;assert r>0
 v=dict(zip(new['witnesses'],[1,0,beta-2,2,2,rank-1,w-1,0,r,0,rank-1,1,0]))
 v.update(beta=beta,K0=K0,MC=MC,MF=MF)
 assert all(v[n]>=0 for n in new['witnesses']) and v['n_s']==0
 e=evaluate(new,v)
 assert (e['R'],e['Y'],e['U'],e['ell'],e['c'],e['k'],e['Bt'],e['Z'],e['Dstar'],e['Q'],e['V'])==(rank,0,0,0,1,k,B,beta,0,9,-1)
 assert all(e[n]==1 for n in ('F0','F1','Fa','Fs')) and e['out']==0
 return v
v=check(2,1,1,1)
assert [v[n] for n in new['witnesses']]==[1,0,0,2,2,43,1,0,229,0,43,1,0]
assert evaluate(old,v)['out']!=0
check(3,2,4,5)
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
a=read(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
b=read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for name,meta in a['ports'].items():
 assert b['ports'][name]['sha256_gzip']==meta['sha256_gzip'] and b['ports'][name]['sha256_raw']==meta['sha256_raw']
 comp=(root/meta['path']).read_bytes();assert digest(comp)==meta['sha256_gzip']
 raw=zlib.decompress(comp,31);assert len(raw)==meta['raw_bytes'] and digest(raw)==meta['sha256_raw']
 ports[name]=int.from_bytes(raw,'little')
assert set(ports)=={'beta','K0','MC','MF'}
check(**ports)
print(json.dumps({'scope':'concrete s=0 counterexamples and graph edit; no global equivalence or Lean theorem','candidate_gates':len(newrows),'inputs':len(new['witnesses']),'extra_toy_controls':1,'toy_parent_nonzero':True,'authenticated_port_witness_zero':True,'decompressed_ports':len(ports)},sort_keys=True,indent=2))
