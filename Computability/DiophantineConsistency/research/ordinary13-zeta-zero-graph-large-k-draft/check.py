from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-zeta-zero-graph-large-k-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
for t in range(350):
 v=[(t*(i+3)+i*i+1)%9 for i in range(13)];v[9]=(t%5)+1;v[10]=0;p=[(t*(j+2)+j)%7+1 for j in range(4)]
 a=ev(v,p);q=1+v[0]*p[0];X=q*v[6];Y=q**3*(v[7]+1);k=v[9];c=k+Y*k;aa=X*Y+Y;delta=3+4*aa+aa*aa
 assert a['kbase']==k and a['c']==c and a['Delta']==delta and (aa+2)**2==delta+1
 assert a['A0']==a['Z']**2-a['qm']**2*(1+(X*Y*Y)*(X*Y*Y+1)*k*k)
 assert a['A1']==a['Dstar']**2-a['U']**2*(1+delta*c*c)
src=(D/'ZetaZeroGraphLargeK.lean.src').read_text()
for x in ['theorem large_k','(hbeta : 0<(p 0:V))','(hzeta : v 10=0) (heta : 0<v 9)','EtaZetaNaturalXPositiveDraft.X_positive','natural_norms_of_graph','ZetaZeroNormLargeKDraft.large_first_ordinate']:
 assert x in src,x
print(json.dumps({'actual_graph_zeta_zero_norm_controls':350,'eta_positive_and_beta_explicit':True,'lean_executed':False,'graph_theorem_checked':False},sort_keys=True,indent=2))
