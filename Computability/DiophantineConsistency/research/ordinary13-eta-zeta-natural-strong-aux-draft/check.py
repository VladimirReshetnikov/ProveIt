from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-natural-strong-aux-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
s0=Path('research/ordinary13-eta-natural-graph-strong-aux-model-draft/EtaNaturalGraphStrongAux.lean.src').read_text()
e=s0.replace('import EtaNaturalGapRank','import EtaZetaNaturalGapRank').replace('import EtaNaturalGraphNorms','import EtaZetaNaturalGraphNorms').replace('EtaNaturalGraphStrongAuxDraft','EtaZetaNaturalGraphStrongAuxDraft').replace('EtaNaturalGraphNormsDraft','EtaZetaNaturalGraphNormsDraft').replace('EtaNaturalGapRankDraft','EtaZetaNaturalGapRankDraft').replace('EtaNaturalXPositiveDraft','EtaZetaNaturalXPositiveDraft').replace('EtaNaturalUnitGraphDraft','EtaZetaNaturalUnitGraphDraft').replace('EtaNaturalUnitBridgeDraft','EtaZetaNaturalUnitBridgeDraft')
assert (D/'EtaZetaNaturalGraphStrongAux.lean.src').read_text()==e
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
cases=0;neg=False
for t in range(500):
 v=[(t*(i+3)+i*i+1)%9 for i in range(13)];v[0]+=1;v[9]+=1;v[10]=0;p=[(t*(j+2)+j)%7+1 for j in range(4)]
 q=1+v[0]*p[0];F=v[1]+1
 if F>q:continue
 a=ev(v,p);Y=q**3*(v[7]+1);k=v[9];c=k+Y*k;T=v[5]+1;ii=v[4]+1;f=v[3];aa=q*v[6]*Y+Y;delta=3+4*aa+aa*aa
 R=((q-1)*(q-F)+(v[2]+1))*(q*q-1)+(p[2]+q*p[3])*v[0]
 z=f*f*(T*c-R)-c
 assert a['V']==z and a['I']==ii*c*c and a['g72']==(ii*c*c)**2-delta*(f*f-1)
 assert a['Fa']==v[11]**2-delta*(f*f-1)*(v[11]**2-z*z)
 neg=neg or z<0;cases+=1
assert neg and cases>0
print(json.dumps({'exact_source_transcription':True,'zeta_zero_field_controls':cases,'negative_signed_ordinate_seen':neg,'geometry_still_explicit':True,'lean_executed':False},sort_keys=True,indent=2))
