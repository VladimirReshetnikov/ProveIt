from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-zero-compact-parity-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s=(D/'ZetaZeroCompactParity.lean.src').read_text();c=(D/'ZetaZeroCompactGraph.lean.src').read_text()
for t in ['(hzeta : v 10=0) (heta : 0<v 9)','let c:=k v+Y p v*k v','compact_rank_window K v hz hk1','compact_early_index K v hz hk1','ZetaZeroParityBoundaryDraft.contradiction_of_facts']:
 assert t in s,t
for t in ['theorem positive_eta_branch','(hzeta : v 10=0) (heta : 0<v 9)','EtaZetaNaturalUnitBridgeDraft.signed_norms','EtaZetaNaturalGraphStrongAuxDraft.direct_auxiliary','ZetaZeroCompactParityDraft.zeta_zero_of_represented_factors','theorem zeta_zero_impossible','by_cases heta : v 9=0','EtaZetaZeroGraphObstructionDraft.both_zero_impossible','theorem zeta_positive']:
 assert t in c,t
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
cases=0
for t in range(400):
 v=[(t*(i+4)+i*i+2)%9 for i in range(13)];v[0]+=1;v[9]=(t%5)+1;v[10]=0;p=[(t*(j+3)+j)%7+1 for j in range(4)]
 q=1+v[0]*p[0];F=v[1]+1
 if F>q:continue
 a=ev(v,p);X=q*v[6];Y=q**3*(v[7]+1);k=v[9];c=k+Y*k;aa=X*Y+Y;delta=3+4*aa+aa*aa
 R=((q-1)*(q-F)+(v[2]+1))*(q*q-1)+(p[2]+q*p[3])*v[0]
 z=v[3]**2*((v[5]+1)*c-R)-c
 assert a['R']==R and a['c']==c and a['V']==z and a['g72']==((v[4]+1)*c*c)**2-delta*(v[3]**2-1)
 assert a['Fa']==v[11]**2-delta*(v[3]**2-1)*(v[11]**2-z*z)
 cases+=1
assert cases>0
print(json.dumps({'changed_graph_parity_field_controls':cases,'zero_eta_branch_explicit':True,'positive_eta_branch_explicit':True,'unelaborated_source_only':True,'lean_executed':False,'endpoint_proved':False},sort_keys=True,indent=2))
