from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta-zero-graph-obstruction-draft')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
src0=Path('research/ordinary13-eta-natural-J-positive-model-draft/EtaNaturalJPositive.lean.src').read_text()
expected=src0.replace('import EtaNaturalUnitBridge','import EtaZetaNaturalUnitBridge').replace('EtaNaturalJPositiveDraft','EtaZetaNaturalJPositiveDraft').replace('EtaNaturalUnitBridgeDraft','EtaZetaNaturalUnitBridgeDraft').replace('EtaNaturalUnitGraphDraft','EtaZetaNaturalUnitGraphDraft').replace('exact generated\neta-natural prototype','exact generated\neta/zeta-natural prototype').replace('prototype factor-unit bridge','probe factor-unit bridge')
assert (D/'EtaZetaNaturalJPositive.lean.src').read_text()==expected
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
def ev(v,p):
 a=dict(zip(g['witnesses'],v));a.update(zip(g['fixed_numerals'],p))
 for n,op,l,r in g['source']:
  x=a[l] if isinstance(l,str) else l;y=a[r] if isinstance(r,str) else r
  a[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return a
for t in range(400):
 v=[(t*(i+4)+i*i+2)%9 for i in range(13)];v[9]=v[10]=0;p=[(t*(j+3)+j)%9 for j in range(4)]
 a=ev(v,p);q=1+v[0]*p[0];Y=q**3*(v[7]+1);U=Y*q*q;X=q*v[6];H=3+4*Y*(X+1)
 R=(v[2]+1+(q-(v[1]+1))*(q-1))*(q*q-1)+v[0]*(p[2]+p[3]*q)
 assert a['R']==R and a['c']==0 and a['Dstar']==U*X+H*(U*v[12]+R+1)
 assert a['A1']==a['Dstar']**2-U**2
src=(D/'EtaZetaZeroGraphObstruction.lean.src').read_text()
for x in ['theorem both_zero_impossible','EtaZetaNaturalJPositiveDraft.J_positive','(hbeta : 0<(p 0:V))','(heta : v 9=0) (hzeta : v 10=0)','EtaZetaNaturalUnitBridgeDraft.signed_norms','ZeroOrdinateMainObstructionDraft.zero_ordinate_impossible']:
 assert x in src,x
print(json.dumps({'J_source_namespace_transcription':True,'actual_graph_double_zero_controls':400,'hbeta_and_both_zero_assumptions_explicit':True,'lean_executed':False,'model_theorem_checked':False},sort_keys=True,indent=2))
