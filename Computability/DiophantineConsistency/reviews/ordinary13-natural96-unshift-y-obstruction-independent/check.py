#!/usr/bin/env python3
"""Independent graph, witness and fixed-byte controls; no Lean run."""
from pathlib import Path
import hashlib,json,operator,zlib
D=Path(__file__).resolve().parents[2]
def digest(b):return hashlib.sha256(b).hexdigest()
def read(p,h):
 b=p.read_bytes();assert digest(b)==h,str(p);return json.loads(b)
a=read(D/'research/ordinary13-natural-cfold97-degree28/candidate.json','8c56deec58c4fbe29ab024fc5a61628ec0d677858c9bc6eb066b4f81244ee2e6')
b=read(D/'research/ordinary13-natural96-unshift-y-obstruction/candidate.json','076e538c34bc2ace133856e7b6ab3a94e885668e381a96ecc48ca92ea8250419')
old={r[0]:r[1:] for r in a['source']};new={r[0]:r[1:] for r in b['source']}
assert len(old)==97 and len(new)==96 and old['Y']==['+','n_Y',1]
assert set(old)-set(new)=={'Y'} and not (set(new)-set(old))
for n,row in new.items():
 op,x,y=old[n];assert row==[op,'n_Y' if x=='Y' else x,'n_Y' if y=='Y' else y],n
assert a['domain']==b['domain']=='nonnegative integers' and a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
known=set(b['witnesses']+b['fixed_numerals']);assert len(known)==17 and len(b['witnesses'])==13
for n,op,x,y in b['source']:
 assert n not in known and op in ('+','-','*') and all(isinstance(v,int) or v in known for v in (x,y))
 known.add(n)
live={b['output']}
for n,op,x,y in reversed(b['source']):
 if n in live:live.update(v for v in (x,y) if isinstance(v,str))
assert all(n in live for n,*_ in b['source']) and set(b['witnesses']+b['fixed_numerals'])<=live
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evaluate(graph,inputs):
 v=inputs.copy()
 for n,op,x,y in graph['source']:
  v[n]=ops[op](v[x] if isinstance(x,str) else x,v[y] if isinstance(y,str) else y)
 return v
# Construct the announced family with explicit quotient/remainder checks.
def witness(beta,K0,MC,MF):
 assert beta>=2 and K0>=1 and MC>0 and MF>0
 _,x=divmod(1-K0,beta)
 if x==0:x=beta
 q=beta+1;rank=(beta-1+beta*beta)*(q*q-1)+MC+MF*q
 B=x+q*(K0-1);quotient,rem=divmod(B,beta)
 assert x>0 and rank>0 and B>0 and rem==0
 r=quotient+1
 inp=dict(zip(b['witnesses'],[1,0,beta-2,2,2,rank-1,x-1,0,r,0,rank-1,1,0]))
 inp.update(beta=beta,K0=K0,MC=MC,MF=MF)
 assert all(inp[n]>=0 for n in b['witnesses']) and inp['n_Y']==0
 e=evaluate(b,inp)
 assert (e['R'],e['U'],e['ell'],e['c'],e['k'],e['C'],e['Bt'])==(rank,0,0,1,rank+1,1,B)
 assert e['Z']==e['M']==q*q*q*beta and (e['Dstar'],e['Q'],e['V'])==(0,9,-1)
 assert (e['A0'],e['A1'],e['Fa'],e['g72'],e['out'])==(0,0,1,0,0)
 return inp
toy=witness(2,1,1,1)
assert [toy[n] for n in b['witnesses']]==[1,0,0,2,2,43,1,0,2,0,43,1,0]
assert evaluate(a,toy)['out']!=0
witness(3,2,4,5)
root=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13'
p72=read(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
p115=read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for name,m in p72['ports'].items():
 assert p115['ports'][name]['sha256_raw']==m['sha256_raw'] and p115['ports'][name]['sha256_gzip']==m['sha256_gzip']
 comp=(root/m['path']).read_bytes();assert digest(comp)==m['sha256_gzip']
 raw=zlib.decompress(comp,31);assert len(raw)==m['raw_bytes'] and digest(raw)==m['sha256_raw']
 ports[name]=int.from_bytes(raw,'little')
assert set(ports)=={'beta','K0','MC','MF'}
witness(**ports)
print(json.dumps({'scope':'concrete Y=0 witnesses and source graph edit; no global equivalence or Lean theorem','candidate_gates':len(new),'inputs':len(b['witnesses']),'extra_toy_controls':1,'toy_parent_nonzero':True,'authenticated_port_witness_zero':True,'decompressed_ports':len(ports)},sort_keys=True,indent=2))
