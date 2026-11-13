from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-natural-early-index-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
r=(D/'EtaZetaNaturalRankIndex.lean.src').read_text();s=(D/'EtaZetaNaturalGraphEarlyIndex.lean.src').read_text()
for text,terms in [(r,['theorem compact_early_index_of_norms','(hk1 : 1≤k v)','have hk : 0<k v := lt_of_lt_of_le','compact_rank_window K v hz hk1','EtaZeroEarlyCongruenceDraft.early_index_of_actual_carrier']),(s,['theorem main_field','theorem main_pair_norm','theorem compact_early_index','(hk1 : 1≤k v)','gap p v hz hbeta hk1',"compact_early_index_of_norms K v tau hz hk1 htau' hm'"])]:
 for x in terms:assert x in text,x
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
cases=0
for t in range(500):
 v=[(t*(i+4)+i*i+2)%7 for i in range(13)];v[0]+=1;v[9]+=1;v[10]=0;p=[(t*(j+3)+j)%7+1 for j in range(4)]
 q=1+v[0]*p[0];F=v[1]+1
 if F>q:continue
 a=ev(v,p);X=q*v[6];Y=q**3*(v[7]+1);k=v[9];c=v[9]+Y*k;aa=X*Y+Y;H=3+4*aa;U=Y*q*q
 R=((q-1)*(q-F)+(v[2]+1))*(q*q-1)+(p[2]+q*p[3])*v[0]
 P=U*(X+aa*c)+H*(U*v[12]+R+1);N=H*k
 assert a['R']==R and a['Dstar']==P-N
 assert a['A1']==(P-N)**2-U**2*(1+(H+aa*aa)*c*c)
 cases+=1
assert cases>0
print(json.dumps({'actual_signed_main_pair_controls':cases,'positive_k_explicit':True,'same_early_witness_interface_present':True,'exact_index_proved':False,'lean_executed':False},sort_keys=True,indent=2))
