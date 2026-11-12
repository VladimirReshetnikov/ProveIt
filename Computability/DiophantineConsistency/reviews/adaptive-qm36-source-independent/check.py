#!/usr/bin/env python3
"""Independent source audit of QM36 conditional transfer and map cases."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
t=pin('research/adaptive-qm36-conditional-model-draft/AdaptiveQM36ConditionalTransfer.lean.src','865a63bdcb03a5f7dc1845bc5af0217529b3d549e7a6e67b73f0f1cf447bc754')
z=pin('research/adaptive-qm36-conditional-model-draft/AdaptiveQM36ParentSlots.lean.src','69bf3f920031a0451740b04c48a68a3ee4edd5708aed84cf85066bf24a23ac78')
m=pin('research/adaptive-qm36-residual-maps-draft/AdaptiveQM36ResidualMaps.lean.src','7fbe29e233c55aa8a3da52ec62030e294d523d4cc820a3ea24195c6926b82432')
f=pin('research/adaptive-qm36-factorized-ring-bridge-draft/AdaptiveQM36FactorizedRingBridge.lean.src','9a7d38b4dc75a13b2bc400214823ceb6d0607ce1c3ab4008d62626de55e912f7')
for path,h in [('research/adaptive-qm36-conditional-model-draft/result.json','7d68f17897e2361f921166aacb4ed32ba183da26667b41a820f53cfdd30bd536'),('research/adaptive-qm36-residual-maps-draft/source-result.json','8e3ce108666e620a4c839a1bfdbf9dee363d3f8e4d323b8c915933470d7e6e49'),('research/adaptive-qm36-factorized-ring-bridge-draft/source-result.json','642993615bc707e46a6893a0a5b46678e8214545cd2b3860fe2f7fb6689bb1aa'),('reviews/adaptive-square-sums36-combined-independent/result.json','4f78edfc16c75a8e690c2cb54ab97f5167ceafebbc5924ea6ed989da6181047a'),('reviews/adaptive-square-sums36-factored-independent/result.json','eefe58d677f5f8a91ccbbb4b8d264cbe10f31be49c787b856d8d3b4a9fb1ae69')]:pin(path,h)
p=json.loads(pin('research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'))
c=json.loads(pin('research/adaptive-square-sums36-combined-shift-quartic/candidate.json','dfa54188a5457f6de2e6d232b2141f12e5f38406bea88e0a5f3f8a07def78523'))
assert [p['witnesses'][i] for i in (0,7,12,15,20,28,33)]==['J','Y','gamma','mainScaleVariable','productVariable','productVariable2','gammaProductVariable']
assert c['witnesses'][20]=='combinedShift'
for i,n in enumerate(c['witnesses']):
 if i!=20:assert n==p['witnesses'][i if i<33 else i+1]
for x in ['if i.val=20 then v 20+v 33','else v ⟨i.val+1, by omega⟩','if i.val=20 then v 28*(1+v 0*beta)','else if i.val=33 then v 15*v 12','else v ⟨i.val-1, by omega⟩','((CurrentWindowCarry2011.ports 0 : ℤ) : DiffRing V)=ι beta','theorem fixed_beta_representation','(h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)','(h37 : AdaptiveQM37ConditionalTransferDraft.GraphZeroObligations)','(h36 : GraphZeroObligations)']:assert x in t,x
for x in ['.mp hz 11','.mp hz 26','v 20=v 28*(1+v 0*beta)','v 33=v 15*v 12','((p 0 : ℤ) : DiffRing V)=ι beta']:assert x in z,x
assert '0<beta' not in t+z+m
def theorem(s,n):
 x=re.search(r'(?ms)^theorem '+re.escape(n)+r'\b(.*?)(?=^theorem |^def |^variable |^end DiophantineConsistency)',s);assert x,n;return x.group(1)
for j in range(27):
 if j in (11,15):continue
 i=j if j<26 else j+1
 q=theorem(m,'same%02d'%j)
 assert f'AdaptiveQM37ResidualsDraft.residuals p {i})' in q and f'AdaptiveQM36Residuals155Draft.residuals p {j})' in q,(i,j)
 assert '((p 0 : ℤ) : DiffRing V)=ι beta' in q
for i in (11,26):assert f'AdaptiveQM37ResidualsDraft.residuals p {i})' in theorem(m,'dropped%02d'%i)
d=theorem(m,'d_relation')
for x in ['AdaptiveQM37ResidualsDraft.residuals p 15)','AdaptiveQM36Residuals155Draft.residuals p 15)','AdaptiveQM36Residuals155Draft.residuals p 11)','3+4*(ι (v 28)+ι (v 7))']:assert x in d,x
def branches(n):return re.split(r'(?m)^  · ',theorem(m,n).split('fin_cases i',1)[1])[1:]
b=branches('extend_zero');assert len(b)==28,len(b)
for i,x in enumerate(b):
 if i in (11,26):assert f'dropped{i:02d} p beta v hbeta' in x
 elif i==15:assert 'd_relation p beta v hbeta' in x and 'hc 15' in x and 'hd' in x
 else:
  j=i if i<26 else i-1
  assert f'same{j:02d} p beta v hbeta' in x and f'hc {j}' in x,(i,j)
b=branches('project_zero');assert len(b)==27,len(b)
for j,x in enumerate(b):
 if j==11:assert 'exact hcombined' in x
 else:
  i=j if j<26 else j+1
  assert f'AdaptiveQM37ResidualsDraft.residuals p {i})' in x and f'using hp {i}' in x,(i,j)
  if j==15:assert 'd_relation p beta (project v) hbeta' in x and 'hcombinedR' in x
  else:assert f'same{j:02d} p beta (project v) hbeta' in x,(i,j)
for i in range(27):
 q=theorem(f,'residual%02d'%i)
 assert f'AdaptiveQM36Residuals153Draft.residuals p {i})' in q and f'AdaptiveQM36Residuals155Draft.residuals p {i})' in q
 assert f'h{i:02d} := residual{i:02d} p v' in theorem(f,'evaluation_identity')
assert '[CommRing R]' in theorem(f,'evaluation_identity') and '(p : Fin 4 → ℤ)' in theorem(f,'evaluation_identity')
for x in ['(h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)','(h37 : AdaptiveQM37ConditionalTransferDraft.GraphZeroObligations)','(h36 : AdaptiveQM36ConditionalTransferDraft.GraphZeroObligations)']:assert x in theorem(f,'native_equivalence')
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',t+z+m+f)
print(json.dumps({'scope':'static source/index audit only; no Lean elaboration or axioms','parent_zero_cases':28,'child_zero_cases':27,'common_residual_lemmas':25,'factored_ring_residuals':27,'beta_cast_equality_required':True,'strict_beta_positivity_required':False,'case_order_assumed':True,'prior_model_obligations_remain_explicit':True},sort_keys=True,indent=2))
