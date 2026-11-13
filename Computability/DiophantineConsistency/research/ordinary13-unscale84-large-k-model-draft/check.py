from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-unscale84-large-k-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary13-qcube-unscale84/candidate.json').read_text())
def ev(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
for t in range(450):
 v=[(t*(i+3)+i*i+1)%9+1 for i in range(13)];p=[(t*(j+2)+j)%7+1 for j in range(4)]
 a=ev(v,p);J,F,alpha=v[:3];X=v[6];s=v[7];eta,zeta,gamma=v[9],v[10],v[12]
 beta,K,MC,MF=p;b=J*beta;q=1+b;Y=q**3*s;k=eta+zeta;c=eta+Y*k;aa=X*Y+Y;delta=3+4*aa+aa**2;u=Y*q*q
 R=(alpha+(q-F)*b)*(q*q-1)+J*(MC+MF*q)
 root=u*(X+aa*c)+(3+4*aa)*(u*gamma+X*Y*q-k+R+1)
 assert a['Dstar']==root and a['A1']==root*root-u*u*(1+delta*c*c)
 assert (X*Y+Y+2)**2==delta+1
src=(D/'Unscale84LargeK.lean.src').read_text()
for s in ['theorem main_form','theorem norm_roots','root_of_scaled_ring_square (b p v)','root_of_scaled_ring_square (u p v)','theorem large_k','first_main_large_k','theorem compact_reverse_inputs','CompactFixedBeta.bounds','theorem compact_positive_zero_iff']:
 assert s in src,s
print(json.dumps({'actual_main_graph_controls':450,'large_k_helper_assumptions_explicit':True,'lean_executed':False,'parent_endpoint_proved':False},sort_keys=True,indent=2))
