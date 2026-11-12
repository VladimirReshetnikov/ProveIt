from pathlib import Path
from hashlib import sha256
import json,random
p=Path('research/ordinary13-natural89-r-replacement-model-draft')
fs=[p/'Natural89RReplacement.lean.src',p/'README.md',
Path('research/ordinary13-natural89-to-positive80-model-draft/Natural89Positive80Transport.lean.src'),
Path('research/ordinary13-natural89-direct-fy-model-draft/Natural89DirectFY.lean.src'),
Path('research/ordinary13-residue-root-switch-extraction-draft/ResidueRootSwitchExtract.lean.src'),
Path('research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),p/'Natural89MixedBridge.lean.src']
s=[f.read_text() for f in fs]
for x in ['def putR','def up','theorem up_putR','theorem zero89_iff85','theorem prototype_update',
 'EtaNaturalUnitBridgeDraft.output_eq','theorem replacement','ResidueRootSwitchExtractDraft.positive_replacement',
 'EtaNaturalGapRankDraft.first_norm','theorem rReplacement','Natural89Positive80TransportDraft.RReplacement K']:
 assert x in s[0],x
assert 'theorem positive_replacement' in s[4]
for x in ['replacement_of_cuts','Natural89DirectFYDraft.directFY','Natural89RReplacementDraft.rReplacement','(h80 : PolynomialBridge','ForcedEta K']:
 assert x in s[8],x
g=json.loads(s[7]);rows={r[0]:r for r in g['source']}
def deps(name,seen=None):
 if isinstance(name,int):return set()
 if name not in rows:return {name}
 _,op,a,b=rows[name];return deps(a)|deps(b)
assert 'n_r' in deps('A0') and all('n_r' not in deps(x) for x in ['A1','Fa','Fs'])
assert rows['out']==['out','-','P0123',1]
rng=random.Random(89888)
for _ in range(500):
 v=[rng.randrange(20) for i in range(13)];r=rng.randrange(20)
 def up(a):
  b=list(a)
  for i in [0,12,6,9]:b[i]+=1
  return b
 def put(a):b=list(a);b[8]=r;return b
 assert up(put(v))==put(up(v)) and put(v)[3]==v[3] and put(v)[11]==v[11]
b,m,k,P,tau=1,3,2,5,7
ell=m*k; z=b*(ell+k-k*P)-P
assert z==-b*tau and tau*tau==1+ell*(ell+k)
r=2*tau;z2=b*(ell+k+r-k*P)-P
assert r>0 and z2==-z and z2*z2==z*z
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'first_only_depends_on_r':True,'coordinate_commutation_controls':500,
 'generic_root_switch_control':True,'lean_executed':False,
 'status':'unelaborated; root extraction, graph reductions and providers remain open'},sort_keys=True,indent=2))
