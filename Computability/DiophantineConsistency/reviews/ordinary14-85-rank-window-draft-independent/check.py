#!/usr/bin/env python3
"""Independent direct 85 rank-window source/finite review; no Lean."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-85-rank-window-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'RankWindow85.lean','abd05c05b598b5e0c9f0ead37993e4f38a4a409304c050f1b4f1a3ef9cb6f30d').decode()
pin(A/'check_source.py','15dc06500862623e3ab53becaf78089dde4af353f833cbf4586ab229a8635094')
receipt=pin(A/'observation.json','058a147e2319f93e42e984c27728a4a4286432bea77d774905f0c6f3df38e671')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-85-rank-window-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='8b9c72390e41c69d539f4b7344bbf83a72b9d67f06f3966fafd5bb4764c887de'
for path,h in {
 'research/ordinary14-85-guard-rank-draft/GuardRank85.lean':'e9eb6ebef3d35dfa2324e00e16a068f7ad67e680f79ebee3a4f8af156e3c6d55',
 'research/ordinary14-84-rank-lower40-draft/RankLower40.lean':'0786421d6d1520e21026e15d36c72ffc00d1c14ebf54bc5c4221ba4e81e9cbd1',
 'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
}.items():pin(D/path,h)
for f in ('(hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P85QcubeGraph.graph p).output v)',
 '40≤R ∧ R+q^3+q+1≤q^4 ∧ R+1<q^4',
 'gap_of_85_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'scalar_rank_window q beta MC MF (v 0) (v 1) (v 2)',
 'RankLower4084Draft.scalar_lower40 q beta (v 0) (v 1) (v 2) MC MF'):
 assert f in src,f
assert 'fields84' not in src and 'FreeJ.zero' not in src
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
for n in ('ordinary14-85-guard-rank-draft-independent','ordinary14-84-rank-lower40-draft-independent'):
 p=D/'reviews'/n;replay(p/'check.py',(p/'result.json').read_bytes())
cases=0;minimum=None
for beta in range(1,5):
 for J in range(1,5):
  q=1+beta*J
  for F in range(1,q):
   for alpha in range(1,q-F):
    for MC in range(beta):
     for MF in range(2*beta):
      R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
      assert R>=40 and R+q**3+q+1<=q**4 and R+1<q**4
      minimum=R if minimum is None else min(minimum,R);cases+=1
assert minimum==40
beta=2;J=1;q=3;F=alpha=X=h=1;K=2;MC=MF=0
R=(alpha+(q-F)*J*beta)*(q*q-1)
assert (q-F-alpha)*(X+K)-F-J*beta*h==0 and R==40 and X%q!=0
print(json.dumps({'scope':'source and finite scalar controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'scalar_cases':cases,
 'minimum_in_grid':minimum,'guard_example_q_not_dividing_X':True},sort_keys=True,indent=2))
