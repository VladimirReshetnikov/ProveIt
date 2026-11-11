#!/usr/bin/env python3
"""Independent compact44 block arithmetic and source pins; no Lean."""
import gzip,hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-c-guard82-probe'
def read(p,h):
 x=p.read_bytes();assert hashlib.sha256(x).hexdigest()==h,p;return x
final_readme=read(A/'README.md','717f18e891420fb469e18c76c01d83698948c42ae6a7b1fe3eabc8caf81db2c2')
link_tail=b'\nIndependent mathematical review is recorded in\n`../../reviews/ordinary14-c-guard82-probe-math-independent/`.\nA separate independent decoder review is recorded in\n`../../reviews/ordinary14-c-guard82-probe-independent/`.\n'
assert final_readme.endswith(link_tail) and hashlib.sha256(final_readme[:-len(link_tail)]).hexdigest()=='6ac02122308f2b1fdfc70d6d4b0bfac559805bc421a9d0648fad4bcb12515e29'
read(A/'check.py','ba6eaf721f92c39cdbc173d2fdd96252bb808af502ca2adb2e41513ac442ce73');receipt=json.loads(read(A/'result.json','ebe1902b44f241a229722b959ce9cd52dac120f13f47c2fca52c6c92b57db85e'))
g=json.loads(read(A/'candidate.json','0f0c1a2be4c62a940384bbae4d16c02caef31d7eefd82dda9ddfb1437236cf57'));assert len(g['source'])==82 and 'K0' not in g['fixed_numerals'] and 'r' in g['witnesses'] and 'omega' in g['witnesses']
parent=json.loads(read(D/'research/ordinary14-shifted-guard87-probe/candidate.json','405dbed5bf465dacac2246e6e8b2c53bcb3dda9b4b13ba277f4a18cdd43ae210'))
expected=[]
for row in parent['source']:
 if row[0] in ('g25','g26','g27','guard_base','bt_quotient'):continue
 expected.append(['guard','-','C','omega'] if row[0]=='guard' else row)
assert g['source']==expected and g['witnesses']==parent['witnesses'] and g['fixed_numerals']==[x for x in parent['fixed_numerals'] if x!='K0']
needed={'guarded_out'}
for name,op,x,y in reversed(expected):
 if name in needed:needed.update((x,y))
assert all(row[0] in needed for row in expected) and all(x in needed for x in g['witnesses']+g['fixed_numerals'])
read(D/'research/current14-carrier64-pell-floor/README.md','8d3b46e7949b7db849a12ef1b6c3586cac661d3158e0347c402581c3b1d08db8');read(D/'research/ordinary13-folded-root86-toy-full-zero/README.md','ce7d50e76f3b035f7fc87ad0228327be9da41d28455e231610f2bd780f473693')
fwd=read(D/'Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean','18b17a1c81e6ff58d74fd6a7160948b75c71203ee8f5c3bd29e4d3fc9a76218a').decode();power=read(D/'Lean/DiophantineConsistency/Compact44/FreeJPowerFinish.lean','e4b2e84586b6232b9accc7775f094d4e1047453f1e8337f6241d39a6657d8816').decode();assert 'let x : Fin 12 → V := ![v 0, v 1, v 2, t, v 5, v 6, v 7, v 8, v 9, v 10, v 4 + v 11, v 12]' in fwd and 'v 5=Exp.exp R' in power
p=D/'con-zfc-diophantine-forms/72-congruence-sextic/positive13';b=json.loads(read(p/'ACTIVE_BINDING.json','6927456a832f956244d4816c20aa96ff0212cb05173f73a11c55e0d8ddc87fbf'));o=json.loads(read(D/'con-zfc-diophantine-forms/115-synchronized-exponents/supplement/coefficients/BINDING.json','dd13365e1c68cd244e67a61abfeb5b351c3ad679acb55a73f714d2885341ee01'));v={}
for n,x in b['ports'].items():
 assert o['ports'][n]['sha256_raw']==x['sha256_raw'] and o['ports'][n]['sha256_gzip']==x['sha256_gzip'];z=read(p/x['path'],x['sha256_gzip']);raw=gzip.decompress(z);assert len(raw)==x['raw_bytes'] and hashlib.sha256(raw).hexdigest()==x['sha256_raw'];v[n]=int.from_bytes(raw,'little')
B=590069; beta,K,MC,MF=(v[n] for n in ('beta','K0','MC','MF'));q=beta+1;HP=MF-beta
assert beta==2**B-1 and 0<MC<beta and 0<HP<beta and 0<=K<q*q
F=q-HP;C=beta-MC;alpha=MC+HP-beta;assert F>0 and C>0 and 0<alpha<beta
G=q*(HP-1)+MC+1;assert G==beta*(q-F)+alpha
R=(G+1)*q*q-1;assert R==G*(q*q-1)+MC+q*MF and R%4==3 and R>=2*B
N=(R-1)//2;assert N.bit_count()==3*B+1 and N.bit_count()==receipt['N_popcount']
e=(R-B)%B;res=(C*(K+pow(2,e,beta))-F)%beta
sha=lambda n:hashlib.sha256(n.to_bytes((n.bit_length()+7)//8,'big')).hexdigest()
assert res and res.bit_length()==receipt['transport_residue_bits'] and sha(res)=='ce55ad184bb41a6cd4d218547b8c3b4950fa42aba22e127057bd2ebbff092f95'
# Independently weighted full-graph modular ray.
prime=1000000007;ray={n:[0,j+1] for j,n in enumerate(g['witnesses'])};ray.update({n:[v[n]%prime] for n in g['fixed_numerals']})
def trim(z):
 while len(z)>1 and z[-1]==0:z.pop()
 return z
def plus(a,b,sign):return trim([((a[j] if j<len(a) else 0)+sign*(b[j] if j<len(b) else 0))%prime for j in range(max(len(a),len(b)))])
def times(a,b):
 z=[0]*(len(a)+len(b)-1)
 for j,x in enumerate(a):
  for k,y in enumerate(b):z[j+k]=(z[j+k]+x*y)%prime
 return trim(z)
def value(x):return [x%prime] if isinstance(x,int) else ray[x]
for name,op,x,y in expected:ray[name]=times(value(x),value(y)) if op=='*' else plus(value(x),value(y),1 if op=='+' else -1)
assert len(ray['guarded_out'])==27 and ray['guarded_out'][-1]!=0
for m in range(1,30):
 for k in range(2,20):assert (m*k+k)**2>1+m*(m+1)*k*k
run=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check.py')],capture_output=True,check=True,timeout=120);assert run.stdout==(A/'result.json').read_bytes()
print(json.dumps({'independent_rank_block_identity':True,'R_bits':R.bit_length(),'N_popcount':N.bit_count(),'weighted_degree':26,'weighted_leader':ray['guarded_out'][-1],'transport_residue_sha256_be':sha(res),'fixed_q_R_exclusion':'conditional on retained-coordinate source replay and graph_power','scope':'external actual-port symbolic probe zero; no unrestricted nonequivalence or Lean'},sort_keys=True,indent=2))
