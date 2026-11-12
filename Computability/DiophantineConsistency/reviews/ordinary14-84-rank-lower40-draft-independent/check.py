#!/usr/bin/env python3
"""Independent rank-40 source and finite review; no Lean invocation."""
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];A=D/'research/ordinary14-84-rank-lower40-draft'
def sha(d):return hashlib.sha256(d).hexdigest()
def pin(p,h):
 d=p.read_bytes();assert sha(d)==h,str(p);return d
src=pin(A/'RankLower40.lean','0786421d6d1520e21026e15d36c72ffc00d1c14ebf54bc5c4221ba4e81e9cbd1').decode()
pin(A/'check_source.py','ae55f59417a96f2d3fa9e596a3f948bb0de25eff35f0b32c2eae09332ff118b6')
receipt=pin(A/'observation.json','6d0edb68c5ccc4a49314702c88f15595f74e30162c18d9c09daca064790ba5bc')
readme=(A/'README.md').read_bytes();tail=(b'\nIndependent source review is recorded in\n'
 b'`../../reviews/ordinary14-84-rank-lower40-draft-independent/`.\n')
assert readme.endswith(tail) and sha(readme[:-len(tail)])=='d6c4f91d7d317c53ae210b3e706afa31f581bfae2e90328555cb9da11ec27777'
pin(D/'research/ordinary14-84-natural-rank-draft/NaturalRank.lean','d9f4c4911951201d5b3b0ed72c02bfc8e5d8b56dcd7dafc378e5273d0686a350')
for f in ('(hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (ha : 0<alpha)',
 '(hq : q=1+J*beta) (hgap : F+alpha<q)',
 'have hgap1 : F+alpha+1≤q := lt_iff_succ_le.mp hgap',
 'tsub_add_cancel_of_le hFq','tsub_add_cancel_of_le hq1',
 'have hqm : 2≤q-1','have hqF : 2≤q-F',
 'have hG : 5≤alpha+(q-F)*(J*beta)','have hsq : 8≤q*q-1',
 'gap_of_84_zero p beta K v hport hK (hv 1) (hv 6) hz',
 '40≤naturalRank beta MC MF v'):
 assert f in src,f
def replay(script,result):
 r=subprocess.run([sys.executable,'-I','-S','-B',str(script)],cwd=D,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=True,timeout=90)
 assert not r.stderr and r.stdout==result
replay(A/'check_source.py',receipt)
p=D/'reviews/ordinary14-84-natural-rank-draft-independent';replay(p/'check.py',(p/'result.json').read_bytes())
cases=0;minimum=None
for beta in range(1,6):
 for J in range(1,5):
  q=1+J*beta
  for F in range(1,q):
   for alpha in range(1,q-F):
    for MC in range(4):
     for MF in range(4):
      G=alpha+(q-F)*J*beta;R=G*(q*q-1)+J*(MC+MF*q)
      assert q>=3 and q-1>=2 and q-F>=2 and G>=5 and q*q-1>=8 and R>=40
      minimum=R if minimum is None else min(minimum,R);cases+=1
assert minimum==40
q=3;F=alpha=w=h=1;J=1;beta=2;K=MC=MF=0
R=(alpha+(q-F)*J*beta)*(q*q-1)
assert (q-F-alpha)*(q*w+K)-F-J*beta*h==0 and R==40
q=2;J=beta=1
assert (0+(q-1)*J*beta)*(q*q-1)<40
assert (1+(q-0)*J*beta)*(q*q-1)<40
print(json.dumps({'scope':'source and finite scalar controls only; no Lean',
 'prelink_readme_sha256':sha(readme[:-len(tail)]),'scalar_cases':cases,
 'minimum_in_grid':minimum,'guard_example_not_graph_zero':True,'positivity_boundaries':True},sort_keys=True,indent=2))
