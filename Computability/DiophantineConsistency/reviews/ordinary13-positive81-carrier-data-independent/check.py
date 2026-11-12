from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive81-carrier-data-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-positive81-carrier-data-model-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
a,b=[json.loads(Path(p).read_text()) for p in ('research/ordinary13-residue-first81/candidate.json','research/ordinary13-qcube-main83/candidate.json')]
assert a['witnesses']==b['witnesses'] and a['fixed_numerals']==b['fixed_numerals']
def ev(g,vs,ps):
 d=dict(zip(g['witnesses'],vs));d.update(zip(g['fixed_numerals'],ps))
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(400):
 v=[(t*(i+3)+i*i+1)%9+1 for i in range(13)]; p=[(t*(j+2)+j)%7+1 for j in range(4)]
 g,h=ev(a,v,p),ev(b,v,p); J,F,alpha=v[:3];beta,K=p[:2]
 q=1+J*beta;X=q*v[6];Y=q**3*v[7];k=v[9]+v[10];ell=X*Y*Y*k;C=q-F-alpha
 P=C*(X+K)-F;Q=C*(X+K*q)-F*q
 assert g['Bt']==P and h['Bt']==Q and Q-P==(q-1)*(C*K-F)
 for f,B in ((g,P),(h,Q)):
  z=(q-1)*(ell+k+v[8]-k*B)-B
  assert f['Z']==z and f['A0']==z*z-(q-1)**2*(1+ell*(ell+k))
nonpositive=0
for bb in range(1,8):
 for ell in range(9):
  for k in range(2,11):
   for r in range(5):
    for P in range(-7,1):
     z=bb*(ell+k+r-k*P)-P
     assert z>=bb*(ell+k)>0 and z*z>bb*bb*(1+ell*(ell+k))
     nonpositive+=1
forward=reverse=0
for q in range(2,18):
 bb=q-1
 for F in range(1,q-1):
  for C in range(1,q-F):
   for K in range(5):
    for X in range(1,q*q+3):
     P=C*(X+K)-F;Q=C*(X+K*q)-F*q
     assert Q-P==bb*(C*K-F)
     if X>=q*q:assert Q>0;forward+=1
     if Q>0:assert P>0;reverse+=1
     assert (P-Q)%bb==0
source=(A/'PositiveCarrierData.lean.src').read_text(); comp=(A/'CompanionCarrierFacts.lean.src').read_text(); fc=(A/'Positive81ForwardCompact.lean.src').read_text()
for tok in ['theorem P_positive','(hk : 2≤k)','natural_magnitude_square z','scaled_quotient','natural_dvd_of_signed','linear_combination hz-hw'] :assert tok in source,tok
for tok in ['theorem enlarged_companion','(hX : q*q≤X)','theorem reduced_companion','(hC : 0<C) (hX : 0<X)','linear_combination hd+(ι C*ι K-ι F)*hqR','linear_combination hd-(ι C*ι K-ι F)*hqR']:assert tok in comp,tok
for tok in ['Positive81To83TransportDraft.prototype_zero_of81','EtaNaturalGapRankDraft.gap','Positive81ExactMainDraft.calibration81_original'] :assert tok in fc,tok
print(json.dumps({'author_receipt_reproduces':True,'literal_graph_controls':400,'nonpositive_carrier_cases':nonpositive,'forward_positivity_cases':forward,'reverse_positivity_cases':reverse,'lean_executed':False,'end_to_end_proof':False},sort_keys=True,indent=2))
