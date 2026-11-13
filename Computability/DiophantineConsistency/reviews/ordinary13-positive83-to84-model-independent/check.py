from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-positive83-to84-model-independent');packet=Path('research/ordinary13-positive83-to84-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(packet/'check.py')])==(packet/'receipt.json').read_bytes()
a,b=[json.loads(Path(p).read_text()) for p in ('research/ordinary13-qcube-main83/candidate.json','research/ordinary13-qcube-unscale84/candidate.json')]
assert a['fixed_numerals']==b['fixed_numerals'] and a['witnesses'][6]=='w' and b['witnesses'][6]=='X'
def ev(g,v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(320):
 v=[(t*(i+4)+i*i+2)%9+1 for i in range(13)];p=[(t*(j+3)+j)%7 for j in range(4)]
 v[12]+=v[6];q=1+v[0]*p[0];w=v[6];u=v.copy();u[6]=q*w;u[12]=v[12]-w
 A,B=ev(a,v,p),ev(b,u,p)
 for name in ('A0','A1','Fa','g72','out'):assert A[name]==B[name]
 back=u.copy();back[6]=w;back[12]=u[12]+w;assert back==v and min(u)>0
 # An independently chosen positive 84 vector with q | X maps back to 83.
 x=[(t*(i+7)+i*i+3)%11+1 for i in range(13)];q=1+x[0]*p[0];w=(t%5)+1;x[6]=q*w
 y=x.copy();y[6]=w;y[12]=x[12]+w
 B,A=ev(b,x,p),ev(a,y,p)
 for name in ('A0','A1','Fa','g72','out'):assert A[name]==B[name]
 assert min(y)>0
s=(packet/'Positive83To84Transport.lean.src').read_text();br=(packet/'Positive83To84Bridge.lean.src').read_text()
for term in ['def GammaCalibration','c p v=ycoord R (a p v)','d=xcoord R (a p v)','k v=R+1+U p v*W','ModifiedCarrierGammaDraft.gamma_gt_from_modified_balance','(hX : v 6=q p v*w)','(hdiv : q p v∣v 6)','(hgamma : v 6<v 12)']:
 assert term in s,term
for term in ['def GammaCut','def CalibrationCut','def DivCut','(hg : GammaCut K) (hd : DivCut K)','(h84 : PolynomialBridge','Positive81To83TransportDraft.CrossRootCut K']:
 assert term in br,term
print(json.dumps({'author_receipt_reproduces':True,'two_way_positive_graph_controls':640,'gamma_divisibility_parent_cuts_explicit':True,'lean_executed':False},sort_keys=True,indent=2))
