#!/usr/bin/env python3
"""Independent auxiliary norm source and finite review; no Lean invocation."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-aux-norm-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'AuxNorm.lean','42f422ac8b96eac7d4d1b8fe6e10bd6c9ec7d3c4a98f6d6f22eeddba9e511ddc').decode()
pin(A/'check_source.py','e02cc99b0c9ccf04a7d83959b8954bda6325eb16e931e1d2c4cc33d4daa61317')
receipt=pin(A/'observation.json','a544b4d39a726da890f52467f2c23edd21505d395b36b607d76451bf235d6a79')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-aux-norm-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='63cae4b41413258a6b9751125da5f09dc27a76cc7caaefe97578eb38274ac3fc'
for path,h in {
 'research/ordinary14-84-natural-rank-draft/NaturalRank.lean':'d9f4c4911951201d5b3b0ed72c02bfc8e5d8b56dcd7dafc378e5273d0686a350',
 'research/ordinary14-84-85-zero-fields-draft/ZeroFields.lean':'75bb11893469673856b6fe02eba6f17317dfa8b4b65d35272577c42cf47b9c1e',
 'research/ordinary14-aux-graph-norm-client-draft/GraphNormClient.lean':'c3350a90b8fa909c208ad197acc7a3bbb15bd3e6d8e45ebf097645ae602ec02e',
 'Lean/DiophantineConsistency/Compact44/P72Aux.lean':'b784a60e125132fcdeabf5b3341827668d44402cc9f0b28c8da8822651517eb4',
 'Lean/DiophantineConsistency/Compact44/P72Exact.lean':'a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3',
}.items():pin(D/path,h)
graph=json.loads(pin(D/'research/ordinary14-qcube84-probe/candidate.json','cc1e1f58416c964d02906af8ef2378f74f1ca94b7806bcc8ae670a31d5f08b61'))
for f in ('(hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v)',
 'let Vp := v 3*v 3*(v 5*c)','let Vn := v 3*v 3*R+c',
 'let Qa := Delta*(v 3*v 3-1)',
 'rank_of_84_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz',
 'P72Root.ι_tsub hf2','(ZeroFields8485Draft.fields84 p v hz).2.2.1',
 'P72Aux.ι_absdiff_sq','linear_combination hcore'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-84-natural-rank-draft-independent','ordinary14-84-85-zero-fields-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in graph['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8401141);pos=neg=0
for _ in range(600):
 v={n:rng.randrange(1,6) for n in graph['witnesses']};v.update({n:rng.randrange(1,6) for n in graph['fixed_numerals']})
 q=1+v['J']*v['beta'];v['F']=rng.randrange(1,q+1)
 data=calc(v);R=data['R'];X=q*v['w'];Y=q**3*v['s'];a=X*Y+Y;c=v['eta']+Y*(v['eta']+v['zeta'])
 v['T']=max(1,R//c+rng.randrange(-2,4));data=calc(v)
 delta=3+4*a+a*a;Vp=v['f']**2*(v['T']*c);Vn=v['f']**2*R+c
 Q=delta*(v['f']**2-1);z=Vp-Vn;u=v['u']
 assert data['Fa']==(z+u)**2-Q*((z+u)**2-z**2)
 assert (data['Fa']==1)==(Q*abs(z)**2+abs(z+u)**2==1+Q*abs(z+u)**2)
 pos+=z>0;neg+=z<0
assert pos and neg
print(json.dumps({'scope':'source and finite auxiliary controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'formula_cases':600,
 'positive_signed_z':pos,'negative_signed_z':neg},sort_keys=True,indent=2))
