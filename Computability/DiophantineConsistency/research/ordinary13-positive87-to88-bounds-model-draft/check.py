from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-positive87-to88-bounds-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary13-aux-root87-36/candidate.json').read_text())
def ev(v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(500):
 v=[(t*(i+3)+i*i+1)%9+1 for i in range(13)];p=[(t*(j+2)+j)%7+1 for j in range(4)]
 g0=ev(v,p);J,F,alpha,f,i,T,X,Y,r,eta,zeta,y,gamma=v;beta,K,MC,MF=p
 b=J*beta;q=1+b;k=eta+zeta;c=eta+Y*k;a=X*Y+Y;delta=3+4*a+a*a;ell=X*Y*(Y*k);M=q**3*b;U=Y*q*q
 R=(alpha+(q-F)*b)*(q*q-1)+J*(MC+MF*q)
 root=U*(X+a*c)+(3+4*a)*(U*gamma+X*Y*q-k+R+1)
 assert g0['A0']==g0['Z']**2-M*M*(1+ell*(ell+k))
 assert g0['Dstar']==root and g0['A1']==root*root-U*U*(1+delta*c*c)
 assert g0['g72']==(i*c*c)**2-delta*(f*f-1)
 assert g0['Q']==delta*(f*f-1) and g0['V']+c==f*f*(T*c-R)
 assert (X*Y+Y+2)**2==delta+1
src=(D/'Positive87To88Bounds.lean.src').read_text()
for tok in ['theorem first_form','theorem main_form','theorem strong_form','theorem common_zero','theorem bounds_of_zero','root_of_scaled_ring_square (scaleFirst p v)','root_of_scaled_ring_square (scaleMain p v)','aux_bounds_of_natural_norms','def PositiveBeta','theorem bounds_cut']:
 assert tok in src,tok
print(json.dumps({'first_main_strong_graph_controls':500,'positive_beta_explicit':True,'lean_executed':False,'endpoint_proved':False},sort_keys=True,indent=2))
