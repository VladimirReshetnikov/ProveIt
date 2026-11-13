#!/usr/bin/env python3
"""Audit named source signatures, without Lean or proof/byte claims."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;D=P.parents[1];L=D/'Lean/DiophantineConsistency'
pins={
 L/'ArithmeticAdaptiveRankWindow2011.lean':'0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794',
 L/'ArithmeticPellFirstNorm.lean':'374719597b3126504fc7b4daeb8ce08a7bae36c911ed37d8fee3d90ed324a5d5',
 L/'ArithmeticPellClassification.lean':'77dc61a25a075c237ea36cc14a3e46c9832a1de827b84427679e268111a4cf78',
 L/'BFS943/Direct80IndexOne.lean':'db0462fd907b629d9720106cfd9ea19fc8fa9e74e659d8286a039affbdc50761',
 L/'BFS943/TraceNormKpos.lean':'c8616ea29abed8cf4beceb426f202fb955557de43422647e47f0bf75df65c1b5',
 L/'Compact44/DirectMainNorm.lean':'29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd',
 D/'research/ordinary14-74-ownzero-product-draft/OwnZeroProduct74.lean':'26404a26b78b3099ddaa407d2eed829d884568821e08a5c7780a1e0ac167a1db',
 D/'research/ordinary14-74-ownzero-guard-strict-draft/OwnZeroGuardStrict74.lean':'d8d99e58177cdc6fde4fad5f79b577ce97023162656931691ce314141f98e1b8',
 D/'research/ordinary14-natural-forced-gamma80/candidate.json':'136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5',
}
sources={}
for path,sha in pins.items():
 b=path.read_bytes();assert hashlib.sha256(b).hexdigest()==sha,str(path);sources[path.name]=b.decode()
checks={
 'ArithmeticAdaptiveRankWindow2011.lean':['theorem scalar_rank_window','(hgap : F+alpha<q)','+q^3+q+1≤q^4'],
 'ArithmeticPellFirstNorm.lean':['theorem positive_parameter_solution','theorem descent','theorem solution_index'],
 'ArithmeticPellClassification.lean':['theorem solution_index'],
 'Direct80IndexOne.lean':['theorem impossible (Y S X eta zeta m : V)','(hk : eta+zeta=2)'],
 'TraceNormKpos.lean':['theorem first_index_ge_two','theorem graph_rank_size','8*P+4≤k v'],
 'DirectMainNorm.lean':['theorem direct_main_orientation (U X Y k eta G R : V)','(hU : 0<U) (hY : 8≤Y) (hk : 0<k)','m*m=1+(H+a*a)*(c*c)'],
 'OwnZeroProduct74.lean':['theorem factor_units_of_zero','(hJ : 0<v 0) (hw : 0<v 6) (hs : 0<v 7)','(hstrong :'],
 'OwnZeroGuardStrict74.lean':['theorem strict_of_zero','(hv : ∀ j, 0<v j)'],
}
for name,needles in checks.items():
 for x in needles:assert x in sources[name],(name,x)
g=json.loads(sources['candidate.json']);assert g['operations']==80 and len(g['witnesses'])==14
print(json.dumps({'scope':'source signatures only; no Lean, model theorem, iPRA or byte binding',
                  'pinned_sources':len(pins),'direct_main_orientation_has_no_positive_gamma_premise':True,
                  'existing_guard_strict_client_requires_all_slots_positive':True},sort_keys=True,indent=2))
