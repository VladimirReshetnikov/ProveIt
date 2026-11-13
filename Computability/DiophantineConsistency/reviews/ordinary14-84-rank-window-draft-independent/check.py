#!/usr/bin/env python3
"""Independent scalar window source/finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-rank-window-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'RankWindow.lean','f0fce525b747e9e053be8752e740ac3171a22f00026cbaa2f14c5ce9cc5f57cb').decode()
pin(A/'check_source.py','2c97572a61f271020cc8dca7c8240b17b4097fb61ba022a5fd6cce79110459d2')
receipt=pin(A/'observation.json','82d77d7bdfb34464f89d2a37a3cbb4dae35a64f3611e9cfbe58653d0f51f71b2')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-rank-window-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='cd4f10903aeb6f20ce3f7073d0ab63c1f7926ef1608fadd8fad7fa9b0d5b3e21'
pin(D/'research/ordinary14-84-natural-rank-draft/NaturalRank.lean','d9f4c4911951201d5b3b0ed72c02bfc8e5d8b56dcd7dafc378e5273d0686a350')
pin(D/'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean','0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794')
for f in ('(hMC : MC<beta) (hMF : MF<2*beta)',
 '(hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v)',
 '24≤R ∧ R+q^3+q+1≤q^4 ∧ R+1<q^4',
 'gap_of_84_zero p beta K v hport hK (hv 1) (hv 6) hz',
 'scalar_rank_window q beta MC MF (v 0) (v 1) (v 2)',
 'hbeta (hv 0) (hv 1) (hv 2) hMC hMF hq hgap'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-natural-rank-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0;minimum=None
for beta in range(1,5):
 for J in range(1,5):
  q=1+beta*J
  for F in range(1,q):
   for alpha in range(1,q-F):
    for MC in range(beta):
     for MF in range(2*beta):
      R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
      assert q>=3 and q-F>=2 and q-1>=2 and R>=40
      assert R+q**3+q+1<=q**4 and R+1<q**4
      minimum=R if minimum is None else min(minimum,R);cases+=1
assert minimum==40
beta=2;J=1;q=3;F=alpha=w=h=1;K=MC=MF=0;X=q*w
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
assert (q-F-alpha)*(X+K)-F-J*beta*h==0 and R==40
print(json.dumps({'scope':'source and finite scalar controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'scalar_cases':cases,
 'minimum_in_grid':minimum,'R40_guard_example_not_graph_zero':True},sort_keys=True,indent=2))
