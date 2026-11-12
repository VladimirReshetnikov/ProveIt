#!/usr/bin/env python3
"""Independent DAG and exact witness audit; no Lean/iPRA claim."""
from pathlib import Path
import hashlib,json,operator,zlib
D=Path(__file__).resolve().parents[2]
def digest(data):return hashlib.sha256(data).hexdigest()
def load(path,h):
 data=(D/path).read_bytes();assert digest(data)==h,str(path);return json.loads(data)
a=load('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5')
b=load('research/ordinary14-natural78-unshift-s-obstruction/candidate.json','f9e0654ed0bdd521796877e0c0ff4addace202de5a78726bcec4bff7dda4fce0')
assert a['domain']==b['domain']=='nonnegative integers'
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']==['beta','K0','MC','MF']
assert a['output']==b['output']=='out' and a['operations']==len(a['source'])==79 and b['operations']==len(b['source'])==78
old={name:[op,x,y] for name,op,x,y in a['source']};new={name:[op,x,y] for name,op,x,y in b['source']}
assert len(old)==79 and len(new)==78 and set(old)-set(new)=={'s'} and set(new)<=set(old)
assert old['s']==['+','n_s',1]
for name,row in new.items():
 op,x,y=old[name];assert row==[op,'n_s' if x=='s' else x,'n_s' if y=='s' else y],name
available=set(b['witnesses']+b['fixed_numerals']);assert len(available)==18
for name,op,x,y in b['source']:
 assert name not in available and op in ('+','-','*') and all(type(z) is int or z in available for z in (x,y))
 available.add(name)
live={'out'}
for name,op,x,y in reversed(b['source']):
 if name in live:live.update(z for z in (x,y) if isinstance(z,str))
assert all(row[0] in live for row in b['source']) and set(b['witnesses']+b['fixed_numerals'])<=live
ops={'+':operator.add,'-':operator.sub,'*':operator.mul}
def evaluate(g,env):
 v=dict(env)
 for n,op,x,y in g['source']:
  assert n not in v
  v[n]=ops[op](x if type(x) is int else v[x],y if type(y) is int else v[y])
 return v
def example(beta,K0,MC,MF):
 assert beta>=2 and K0>=0 and MC>0 and MF>0
 q=beta+1; w=(1-K0)%beta or beta
 rank=(beta**2+beta-1)*(q*q-1)+MC+MF*q
 assert w>0 and rank>0 and (q*w+K0-1)%beta==0
 h=(q*w+K0-1)//beta; assert h>=0
 v={'n_J':1,'n_F':0,'n_alpha':beta-2,'n_f':2,'n_i':2,'n_T':rank-1,'n_w':w,'n_s':0,
    'n_r':1,'n_eta':0,'n_zeta':rank-1,'n_y':1,'n_gamma':1,'n_h':h,
    'beta':beta,'K0':K0,'MC':MC,'MF':MF}
 assert set(v)==set(b['witnesses']+b['fixed_numerals']) and all(v[n]>=0 for n in b['witnesses'])
 e=evaluate(b,v)
 expected={'qm':beta,'q':q,'X':q*w,'Y':0,'U':0,'ell':0,'c':1,'k':rank+1,'R':rank,
  'Dstar':0,'Q':9,'V':-1,'F0':1,'F1':1,'Fa':1,'Fs':1,'guard':1,'out':0}
 for n,x in expected.items():assert e[n]==x,n
 return v
toy=example(2,1,1,1)
assert tuple(toy[n] for n in b['witnesses'])==(1,0,0,2,2,43,2,0,1,0,43,1,1,3)
assert evaluate(a,toy)['out']!=0
# Extra controls in different congruence classes, not an exhaustive proof.
example(3,0,2,1);example(7,11,1,8)
root=Path('con-zfc-diophantine-forms/72-congruence-sextic/positive13')
p72=load(root/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf')
p115=load('con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01')
ports={}
for n,meta in p72['ports'].items():
 assert all(meta[k]==p115['ports'][n][k] for k in ('sha256_raw','sha256_gzip','raw_bytes','bits'))
 compressed=(D/root/meta['path']).read_bytes();raw=zlib.decompress(compressed,31)
 assert digest(compressed)==meta['sha256_gzip'] and digest(raw)==meta['sha256_raw'] and len(raw)==meta['raw_bytes']
 ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==meta['bits']
assert set(ports)=={'beta','K0','MC','MF'}
example(**ports)
print(json.dumps({'scope':'concrete zero-witness obstruction only; no global-existence, Lean or PDF claim',
 'parent_gates':79,'probe_gates':78,'all_gates_inputs_ports_live':True,
 'toy_parent_same_vector_nonzero':True,'additional_toy_controls':2,'authenticated_port_zero':True,
 'authenticated_ports':len(ports)},sort_keys=True,indent=2))
