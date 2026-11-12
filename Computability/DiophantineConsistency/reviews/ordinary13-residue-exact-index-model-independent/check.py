#!/usr/bin/env python3
"""Exact-index client source argument and explicit premise audit; no Lean."""
import hashlib,json,sys
from pathlib import Path
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src','dc941fd8914795ac46f513f45979ef7c69c22a6d1be4dc332605f1ddb7a3a79a')
pin('research/ordinary13-residue-exact-index-model-draft/receipt.json','db4dff7a02d19777927fd80f70093c36dc51b5f6d09409093d93918994857e81')
pin('reviews/ordinary13-residue-main-congruence-model-independent/result.json','d5e8f827520f00bc6d7c5d4a8a8759d265a9dd43c48e0fb5a31ca2147192f8d1')
p=pin('Lean/DiophantineConsistency/Compact44/P72Exact.lean','a07730d92aefd39d86083d037f4772bacd7741788e2fff1f7669d33fa0ad05d3')
c=pin('Lean/DiophantineConsistency/ArithmeticPellClassification.lean','77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78')
for x in ['theorem main_index_of_natural_norm','ArithmeticPellClassification.solution_index a g c hg','theorem exact_indices_of_actual_graph','(hR26 : 26≤rank p v)','(hi\' : 0<i\') (hf : 0<v 3)','(hmy : ycoord mainIndex (a p v)=c p v)','(hg : g*g=1+','(hstrong :','(haux :','ResidueMainCongruenceDraft.early_index_of_actual_graph','P72Exact.indices_ordinary','(v 7+1) i\' (v 3) (v 5+1) u n s ((q p v)^4) mainIndex (v 9+1)','hq3 hX hy0 hY heta hc hi\' hf haa hR26 hny\' hks\' hmu hnmod hmy hg hstrong haux']:
 assert x in s,x
assert '(hη : 0 < η)' in p and 'ycoord time b=y' in c
assert 'Bez' not in s and 'q ∣' not in s
# Discriminant used by exact ordinary strong clients: delta(a)=a²+4a+3.
for a in range(40):assert (a+2)**2-1==(3+4*a)+a*a
print(json.dumps({'scope':'source tuple, explicit fact hypotheses and bounded discriminant controls; no Lean','parent_eta_stays_positive_in_client':True,'main_norm_index_strong_auxiliary_explicit':True,'R_at_least_26_explicit':True,'no_later_bezout_claim':True,'actual_graph_source_unelaborated':True,'lean_elaborated':False},sort_keys=True,indent=2))
