from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-natural-X-positive-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s0=Path('research/ordinary13-eta-natural-X-positive-model-draft/EtaNaturalXPositive.lean.src').read_text()
expected=s0.replace('import EtaNaturalJPositive','import EtaZetaNaturalJPositive').replace('EtaNaturalXPositiveDraft','EtaZetaNaturalXPositiveDraft').replace('EtaNaturalJPositiveDraft','EtaZetaNaturalJPositiveDraft').replace('EtaNaturalUnitBridgeDraft','EtaZetaNaturalUnitBridgeDraft').replace('EtaNaturalUnitGraphDraft','EtaZetaNaturalUnitGraphDraft').replace('def k (v : Fin 13 → V) : V := v 9+v 10+1','def k (v : Fin 13 → V) : V := v 9+v 10').replace('ι (U p v)*ι (v 12)-((ι (v 9)+ι (v 10))-rankRing p v)','ι (U p v)*ι (v 12)-((ι (v 9)+ι (v 10))-rankRing p v-1)').replace('exact eta-natural graph X>0','exact eta/zeta-natural graph X>0').replace('shifted zeta is v10+1>0','zeta=v10 may be zero')
assert (D/'EtaZetaNaturalXPositive.lean.src').read_text()==expected
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
for t in range(400):
 v=[(t*(i+5)+i*i+1)%9 for i in range(13)];v[6]=0;p=[(t*(j+3)+j)%7 for j in range(4)]
 a=ev(v,p);q=1+v[0]*p[0];Y=q**3*(v[7]+1);U=Y*q*q;k=v[9]+v[10];c=v[9]+Y*k
 R=(v[2]+1+(q-(v[1]+1))*(q-1))*(q*q-1)+v[0]*(p[2]+p[3]*q)
 shift=U*v[12]-(k-R-1)
 assert a['kbase']==k and a['c']==c and a['R']==R and a['shift']==shift
 assert a['Dstar']==U*Y*c+(3+4*Y)*shift
 assert a['A1']==a['Dstar']**2-U**2*(1+(3+4*Y+Y*Y)*c*c)
print(json.dumps({'exact_source_transcription_checked':True,'x_zero_graph_controls':400,'zeta_zero_permitted':True,'lean_executed':False,'model_theorem_checked':False},sort_keys=True,indent=2))
