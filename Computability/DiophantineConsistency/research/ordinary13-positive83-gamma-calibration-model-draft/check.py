from pathlib import Path
from hashlib import sha256
import json,random,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
PINS={'research/ordinary13-qcube-main83/candidate.json': 'd19de596305c838c4b58f011a7fd233fedc4f7a7a87923cca60d00f46b408789', 'research/ordinary13-residue-first81/candidate.json': '067d3cf0e92961d272e9018dde38bbe8b00ad55ec8e9145fbdd34c0f13e18352', 'research/ordinary13-eta-zero-graph-adapter-audit/prototype.json': '97273735d1537b597544604d19969630c8464469e9a3ab2f8825f52dc602a648', 'research/ordinary13-positive83-to84-model-draft/Positive83To84Transport.lean.src': '3797f24766c0842839c6c0dff4bc40cfc7a3e959edbdf578b5b16c2f918cea7a', 'research/ordinary13-positive83-to84-model-draft/Positive83To84Bridge.lean.src': '25c422df0ada61b60049e7ccc2cdfbb6ea1ab52060c40c9ba1d57f9fa37dac17', 'research/ordinary13-positive83-reverse-root-model-draft/Positive83CrossRoot.lean.src': 'f47267da5ad69cb0c8725f82a6083a0adab4330d6200f8fc439614ffdea182ac', 'research/ordinary13-positive81-exact-main-model-draft/Positive81ExactMain.lean.src': 'f9a294400eaa1dab6f339f2d746f8ef89e69146f82057baba899513db6cb9686', 'research/ordinary13-positive81-to83-model-draft/Positive81To83Transport.lean.src': 'a01d62a2d5572c712c37bb8a4a933bea26f494b143f104bcbe484a58523f7ae0', 'research/ordinary13-eta-natural-graph-early-index-model-draft/EtaNaturalGraphEarlyIndex.lean.src': '6be2ab639c7b3b41eb81e52740dc54124a50fa35def7e62f5202a1d6e4bbe6d7', 'research/ordinary13-positive81-calibration-model-draft/Positive81Calibration.lean.src': 'fe9386694b4ea07e10ea94b6cd8c3810cb70d394e0bfedd985d358183a753086', 'research/ordinary13-positive83-gamma-calibration-model-draft/Positive83GammaCalibration.lean.src': '483ee5f55a975ff49644cc027bdb97de1cf4ea28ab42255c344a8dbbac96c6c4'}
for p,h in PINS.items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
files=list(PINS); g83,g81,g85=(json.loads(Path(p).read_text()) for p in files[:3])
assert [len(g['source']) for g in (g83,g81,g85)]==[83,81,85]
assert g83['witnesses']==g81['witnesses'] and g85['witnesses']==['n_'+w for w in g81['witnesses']]
ra,rb=({r[0]:r for r in g['source']} for g in (g83,g81))
assert all(ra[n]==rb[n] for n in ra.keys() & rb.keys() if n not in ('g26','Bt'))
for row in [['q','+',1,'qm'],['X','*','q','w'],['q3','*','q','q2'],['Y','*','q3','s'],['U','*','Y','q2'],['E','*','X','Y'],['g44','*','qF','qm'],['G','+','alpha','g44'],['g47','*','G','g46'],['g50','*','J','g49'],['R','+','g47','g50']]:assert ra[row[0]]==row
def ev(g,v,p):
 e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],p))
 for name,op,x,y in g['source']:
  x=x if isinstance(x,int) else e[x];y=y if isinstance(y,int) else e[y]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return e
rng=random.Random(838185);used=0
for _ in range(180):
 v=[rng.randrange(1,5) for _ in range(13)];p=[rng.randrange(1,6) for _ in range(4)]
 v[1]=1;v[2]=1;p[0]=max(p[0],3);r=rng.randrange(1,7);z=v.copy();z[8]=r
 e=[z[i]-1 if i in {1,2,4,5,7,10} else z[i] for i in range(13)]
 A,B,C=ev(g83,v,p),ev(g81,z,p),ev(g85,e,p)
 for name in ('q','X','Y','U','R','k','c','g72','A1','Fa'):assert A[name]==B[name]==C[name],name
 for i in range(13):assert e[i]+(1 if i in {1,2,4,5,7,10} else 0)==(r if i==8 else v[i])
 Q=A['q'];X=A['X'];Y=A['Y'];U=A['U'];rank=((Q-1)*(Q-v[1])+v[2])*(Q*Q-1)+(p[2]+Q*p[3])*v[0]
 assert rank==A['R']
 w=rng.randrange(0,6);W=4*X*Q*v[7]*w
 assert 4*(X*Y*Y)*w==U*W
 used+=1
s=[Path(x).read_text() for x in files[3:]]
assert 'def GammaCalibration' in s[0] and 'def CalibrationCut' in s[1]
assert 'theorem reverse (K : ℕ)' in s[2] and 'theorem exact_and_main' in s[3]
assert 'theorem compact_early_index' in s[5] and 'def OrientedMainCut' in s[6]
assert 'theorem calibration_of_root' in s[7] and 'theorem calibrationCut' in s[7]
print(json.dumps({'sha256':PINS,'exact_83_81_nonfirst_rows_checked':True,'non_r_coordinate_and_rank_controls':used,'W_factor_identity_controls':used,'lean_executed':False,'status':'Unelaborated source composition; all model/provider premises and q-divisibility remain open.'},sort_keys=True,indent=2))
