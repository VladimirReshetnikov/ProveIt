#!/usr/bin/env python3
"""Independent direct 85 main balance source/finite review; no Lean."""
import hashlib,json,random,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-main-balance-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'MainBalance85.lean','686f10c3ff4d86433d8de75ed4897cda3ab9341824ff70213439eba3dc39d317').decode()
pin(A/'check_source.py','ab22d25c5c26c470a5e9160840ef4e32a772f38ccb16f901dce66a92994751d4')
receipt=pin(A/'observation.json','9a8591272ab377a196ecb945e7858e5f3c7fd9d86b076688fc96463ffc8ded8f')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-main-balance-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='ae81d47ddefd88c9f3064e03a7541078d35246793ee961c79134ec4cd20e72f2'
for path,h in {
 'ordinary14-85-direct-norms-draft/DirectNorms85.lean':'2b07f618dc5e76fd6e274596d4425c5c76dbd60919014febb024a9a99265c622',
 'ordinary14-85-guard-rank-draft/GuardRank85.lean':'e9eb6ebef3d35dfa2324e00e16a068f7ad67e680f79ebee3a4f8af156e3c6d55',
 'ordinary14-84-qcube-size-draft/QCubeSize.lean':'6553261e396c24659988420260324bc19911ade97854405e863db4bfb6e510cc',
 'ordinary14-scaled-signed-root-draft/SignedScaledRoot.lean':'900ff0f8acda716fe01f96ffdd463636fae411149df172946e1c34d27ab8cadd',
}.items():pin(D/'research'/path,h)
pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveMainOrientation2011.lean','ad8a0d17ccf06c2f75ce8b095698b66f79869041ae07cf9ff0a376894b4c3968')
g=json.loads(pin(D/'research/ordinary14-qcube85-tradeoff/candidate.json','0f302fc8d7fe4dea66ec48c9e29def6a4d6737d536ddf0cf8043bd7627a985c7'))
for f in ('ι (X v*Y beta v*q beta v)',
 '(hv : ∀ j, 0<v j)','(hz : InternalZero (P85QcubeGraph.graph p).output v)',
 'rank_of_85_zero p beta K MC MF v hport hK hMC hMF (hv 1) (hv 6) hz',
 'main_parts_positive (U beta v) (X v) (Y beta v) (k v) (v 9) (v 12) (q beta v) R hU hY8 hk',
 '(ZeroFields8485Draft.fields85 p v hz).2.1',
 'scaled_signed_root (U beta v)', 'neg_nonpos.mpr (ι_nonneg _)',
 'H*(U beta v*v 12+X v*Y beta v*q beta v+R+1)',
 'apply ι_injective'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-direct-norms-draft-independent','ordinary14-84-qcube-size-draft-independent','ordinary14-scaled-signed-root-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
def calc(v):
 z=v.copy()
 for n,op,x,y in g['source']:
  x=z[x] if isinstance(x,str) else x;y=z[y] if isinstance(y,str) else y
  z[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return z
rng=random.Random(8501031);nondiv=0
for _ in range(500):
 v={n:rng.randrange(1,7) for n in g['witnesses']+g['fixed_numerals']}
 q=1+v['J']*v['beta'];v['F']=rng.randrange(1,q+1);z=calc(v)
 X=v['X'];Y=q**3*v['s'];U=Y*q*q;k=v['eta']+v['zeta'];a=X*Y+Y;c=v['eta']+Y*k
 H=3+4*a;delta=H+a*a;R=z['R'];main=U*(X+a*c)+H*(U*v['gamma']+X*Y*q-k+R+1)
 assert Y>=8 and main>0 and z['A1']==main*main-U*U*(1+delta*c*c)
 assert main+H*k==U*(X+a*c)+H*(U*v['gamma']+X*Y*q+R+1)
 nondiv+=X%q!=0
assert nondiv
print(json.dumps({'scope':'source and finite main-field controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'literal_controls':500,
 'X_not_divisible_by_q':nondiv},sort_keys=True,indent=2))
