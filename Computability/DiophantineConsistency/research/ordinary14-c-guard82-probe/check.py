#!/usr/bin/env python3
"""C-guard speculative graph, actual-port seed and modular degree control; no Lean."""
import gzip,hashlib,json,random
from pathlib import Path
D=Path(__file__).resolve().parents[2];H=Path(__file__).resolve().parent
def load(p,h):
 raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==h;return json.loads(raw)
c=load(H/'candidate.json','0f0c1a2be4c62a940384bbae4d16c02caef31d7eefd82dda9ddfb1437236cf57')
p=load(D/'research/ordinary14-shifted-guard87-probe/candidate.json','405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210')
assert c['witnesses']==p['witnesses'] and c['fixed_numerals']==[x for x in p['fixed_numerals'] if x!='K0']
expect=[]
for row in p['source']:
 if row[0] in ('g25','g26','g27','guard_base','bt_quotient'):continue
 if row[0]=='guard':expect.append(['guard','-','C','omega'])
 else:expect.append(row)
assert c['source']==expect and len(c['source'])==82
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
assert deg['guard']==1 and deg['guard2']==2
p72=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=load(p72/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf');b115=load(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01');fixed={}
for n,m in b['ports'].items():
 assert b115['ports'][n]['sha256_raw']==m['sha256_raw'] and b115['ports'][n]['sha256_gzip']==m['sha256_gzip']; z=(p72/m['path']).read_bytes();assert hashlib.sha256(z).hexdigest()==m['sha256_gzip'];x=gzip.decompress(z);assert len(x)==m['raw_bytes'] and hashlib.sha256(x).hexdigest()==m['sha256_raw'];fixed[n]=int.from_bytes(x,'little')
beta=fixed['beta']; K=fixed['K0'];MC=fixed['MC'];MF=fixed['MF'];B=beta.bit_length();q=beta+1
HP=MF-beta;C=beta-MC;F=q-HP;alpha=q-F-C
assert 0<=K<q*q
assert B==590069 and beta==(1<<B)-1 and 0<MC<beta and 0<HP<beta and C>0 and F>0 and 0<alpha<beta
G=beta*(q-F)+alpha;R=G*(q*q-1)+MC+q*MF;N=(R-1)//2;e=(R-B)%B
assert R%4==3 and N.bit_count()==3*B+1 and R>=2*B
residue=(C*(K+(1<<e))-F)%beta
assert residue!=0 and residue.bit_length()==590003
assert hashlib.sha256(R.to_bytes((R.bit_length()+7)//8,'big')).hexdigest()=='5f058f88f3dddbc69548e694a0272e769417868341adaf1560bf7a41cd36d0f5'
assert hashlib.sha256(residue.to_bytes((residue.bit_length()+7)//8,'big')).hexdigest()=='ce55ad184bb41a6cd4d218547b8c3b4950fa42aba22e127057bd2ebbff092f95'
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
print(json.dumps({'operations':82,'variables':14,'all_gates_inputs_ports_live':True,'K0_less_than_q_min_squared':True,'guard_degree_upper':2,'R_bit_length':R.bit_length(),'R_mod4':R%4,'N_popcount':N.bit_count(),'B':B,'transport_residue_nonzero':True,'transport_residue_bits':residue.bit_length(),'prime':prime,'ray_degree':26,'ray_leader':v['guarded_out'][-1],'scope':'external C-guard graph and scalar seed; full symbolic zero submitted for review; unrestricted equivalence unresolved; no Lean/PDF binding'},sort_keys=True,indent=2))
