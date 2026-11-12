#!/usr/bin/env python3
"""Independent direct 85 auxiliary source/finite review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-aux-norm-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'AuxNorm85.lean','d2630b6fdd8450042d4c1dff24e119d1fd01b2ed92c23c82097917cefa4716c7').decode()
pin(A/'check_source.py','80e0321094a8dd649793923402c3c37af71498e0f757b54cb1f1a1939944fa42')
receipt=pin(A/'observation.json','9294bdd43221cd1294e8e9c6a52b9158064ad34bb5e02d55d6fd7eb0f25f6201')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-aux-norm-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='d6895fe3c592dc2cba5c6210521bba79bc82adefd7dc71b62c645844528fcc0d'
for path,h in {
 'research/ordinary14-85-guard-rank-draft/GuardRank85.lean':'e9eb6ebef3d35dfa2324e00e16a068f7ad67e680f79ebee3a4f8af156e3c6d55',
 'research/ordinary14-85-direct-norms-draft/DirectNorms85.lean':'2b07f618dc5e76fd6e274596d4425c5c76dbd60919014febb024a9a99265c622',
 'research/ordinary14-84-85-zero-fields-draft/ZeroFields.lean':'75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
 'Lean/DiophantineConsistency/Compact44/P72Aux.lean':'b784a60e125132fcdeabf5b3341827668d44402cc9f0b28c8da8822651517eb4',
}.items():pin(D/path,h)
g=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
for f in ('(hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'let c := DirectNorms85Draft.c beta v','let Delta := DirectNorms85Draft.Delta beta v',
 'let Vp := v 3*v 3*(v 5*c)','let Vn := v 3*v 3*R+c',
 'GuardRank85Draft.rank_of_85_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz',
 'P72Root.ι_tsub hf2','(ZeroFields8485Draft.fields85 p v hz).2.2.1',
 'P72Aux.ι_absdiff_sq','linear_combination hcore'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-85-guard-rank-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8501041);pos=neg=nondiv=0
for _ in range(600):
 v={n:rng.randrange(1,7) for n in g['witnesses']+g['fixed_numerals']}
 q=1+v['J']*v['beta'];v['F']=rng.randrange(1,q+1);data=calc(v);R=data['R']
 X=v['X'];Y=q**3*v['s'];a=X*Y+Y;c=v['eta']+Y*(v['eta']+v['zeta'])
 v['T']=max(1,R//c+rng.randrange(-2,4));data=calc(v)
 delta=3+4*a+a*a;Vp=v['f']**2*(v['T']*c);Vn=v['f']**2*R+c
 Q=delta*(v['f']**2-1);z=Vp-Vn;u=v['u']
 assert data['Fa']==(z+u)**2-Q*((z+u)**2-z**2)
 assert (data['Fa']==1)==(Q*abs(z)**2+abs(z+u)**2==1+Q*abs(z+u)**2)
 pos+=z>0;neg+=z<0;nondiv+=X%q!=0
assert pos and neg and nondiv
print(json.dumps({'scope':'source and finite auxiliary controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'formula_cases':600,
 'positive_signed_z':pos,'negative_signed_z':neg,'X_not_divisible_by_q':nondiv},sort_keys=True,indent=2))
