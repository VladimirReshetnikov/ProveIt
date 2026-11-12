#!/usr/bin/env python3
"""Inspect fact-level source hypotheses and sample size implications; no Lean."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1]
def pin(path,sha):
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);return b.decode()
s=pin(P/'GammaPremises.lean','cfdbb97e748edbef9a8bf121cc3e44ac09bc91dc1e60e362b32d675df7ad7192')
pin(D/'research/ordinary14-natural80-gamma-narrow-draft/GammaZeroNarrow.lean','f64c3701ac0894998823fee6eaf7497549aa73b7448ae26b327983b6155642a7')
pin(D/'Lean/DiophantineConsistency/ArithmeticPellClassification.lean','77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78')
pin(D/'Lean/DiophantineConsistency/BFS943/Direct80IndexOne.lean','db0462fd907b629d9720106cfd9ea19fc8fa9e74e659d8286a039affbdc50761')
for x in ('theorem large_ordinate_of_two_norms','(hfirst :','(hmain :',
          'ArithmeticPellClassification.solution_index a d c hmain\'',
          'Direct80IndexOne.impossible Y (a+1) 0 eta zeta j',
          'positive_parameter_solution m tau k hm hfirst',
          'first_ordinate_lower m n k hm hn2 hcoord','theorem narrow_inequalities',
          '(hR : R+q^3+q+1≤q^4)',
          '#print axioms DiophantineConsistency.GammaPremisesDraft.large_ordinate_of_two_norms',
          '#print axioms DiophantineConsistency.GammaPremisesDraft.narrow_inequalities'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
controls=0
for q in range(2,9):
 for X in range(q,q+4):
  for scale in range(1,4):
   Y=q**3*scale;m=X*Y*Y;k=8*m+4;R=q**4-q**3-q-1;eta=1
   assert R+q**3+q+1<=q**4 and R+1<k and X<eta+Y*k
   controls+=1
print(json.dumps({'scope':'unelaborated fact-level source and finite size controls only',
                  'norms_and_rank_bounds_explicit':True,'size_controls':controls,
                  'axiom_prints_not_executed':2,'no_graph_model_ipra_or_byte_claim':True},sort_keys=True,indent=2))
