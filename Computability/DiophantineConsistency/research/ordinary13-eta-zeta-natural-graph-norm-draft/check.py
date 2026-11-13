from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-natural-graph-norm-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s0=Path('research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src').read_text()
e=s0.replace('import EtaNaturalXPositive','import EtaZetaNaturalXPositive').replace('EtaNaturalGraphNormsDraft','EtaZetaNaturalGraphNormsDraft').replace('EtaNaturalUnitGraphDraft','EtaZetaNaturalUnitGraphDraft').replace('EtaNaturalXPositiveDraft','EtaZetaNaturalXPositiveDraft').replace('EtaNaturalUnitBridgeDraft','EtaZetaNaturalUnitBridgeDraft').replace('EtaNaturalJPositiveDraft','EtaZetaNaturalJPositiveDraft').replace('Actual eta-natural prototype graph-to-natural first/main norms.','Actual eta/zeta-natural prototype graph-to-natural first/main norms.').replace('Eta remains a natural input and can be zero.','Eta and zeta remain natural inputs and can be zero.')
assert (D/'EtaZetaNaturalGraphNorms.lean.src').read_text()==e
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 d=dict(zip(g['witnesses'],v));d.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=d[l] if isinstance(l,str) else l;y=d[r] if isinstance(r,str) else r
  d[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
for t in range(400):
 v=[(t*(i+3)+i*i+1)%9 for i in range(13)];p=[(t*(j+2)+j)%7 for j in range(4)];a=ev(v,p)
 b=v[0]*p[0];q=1+b;X=q*v[6];Y=q**3*(v[7]+1);k=v[9]+v[10];m=X*Y*Y;U=Y*q*q;c=v[9]+Y*k;aa=X*Y+Y;delta=3+4*aa+aa*aa
 assert a['qm']==b and a['kbase']==k and a['ell']==m*k and a['U']==U and a['c']==c and a['Delta']==delta
 assert a['A0']==a['Z']**2-b*b*(1+m*(m+1)*k*k)
 assert a['A1']==a['Dstar']**2-U*U*(1+delta*c*c)
print(json.dumps({'exact_namespace_transcription':True,'graph_field_norm_controls':400,'zeta_zero_permitted':True,'lean_executed':False},sort_keys=True,indent=2))
