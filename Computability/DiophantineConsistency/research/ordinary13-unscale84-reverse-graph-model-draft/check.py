from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-unscale84-reverse-graph-model-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
fs=['research/ordinary13-qcube-unscale84/candidate.json','research/ordinary13-aux-root87-36/candidate.json']
a,b=[json.loads(Path(f).read_text()) for f in fs]
def ev(g,v,p):
 x=dict(zip(g['witnesses'],v));x.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  l=x[l] if isinstance(l,str) else l;r=x[r] if isinstance(r,str) else r
  x[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]()
 return x
for t in range(350):
 v=[(t*(i+4)+i*i+2)%9+1 for i in range(13)];p=[(t*(j+3)+j)%7+1 for j in range(4)]
 g=ev(a,v,p); b0=v[0]*p[0];q=1+b0;Y=q**3*v[7];k=v[9]+v[10];ell=v[6]*Y**2*k;P=g['Bt']
 z=b0*(ell+k+v[8]-k*P)-P
 assert g['Z']==z and g['A0']==z*z-b0*b0*(1+ell*(ell+k))
 r=(t%7)+1;w=v.copy();w[7]=Y;w[8]=r;h=ev(b,w,p)
 zshift=b0*(ell+k+r+v[7]-k*P)-P
 assert h['Z']==q**3*zshift and h['A0']==q**6*(zshift*zshift-b0*b0*(1+ell*(ell+k)))
src=(D/'Unscale84ReverseGraph.lean.src').read_text()
for term in ['theorem source_root','theorem source_first','theorem target_first','theorem reverse_root_of_large','shifted_root_of_qcube','(hbeta : 0<(p 0:V))','(hlarge : 8*X v*Y p v*Y p v+4≤k v)','def ReverseInputs','theorem reverse_cut']:
 assert term in src,term
print(json.dumps({'source_target_graph_controls':350,'beta_and_large_k_explicit':True,'lean_executed':False,'endpoint_proved':False},sort_keys=True,indent=2))
