#!/usr/bin/env python3
"""Check exact changed-valuation source delta and client directions, no Lean."""
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[2]
def pin(p,h):
 b=(D/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s=pin('research/ordinary14-natural79-wshift-model-draft/Natural79WShift.lean','7635b50c819f665a6d9410758b3db01c70d3b42c1fff2aee6f3733263f76d7a1')
a=json.loads(pin('research/ordinary14-natural-forced-w79/candidate.json','0d047283e1aed25040871e7d0b797ac168e5f80c596d4551fec916d48fe84cb5'))
b=json.loads(pin('research/ordinary14-natural-forced-gamma80/candidate.json','136560324b95b3fda68d10ebe49bdba0a02e950e0bf6b7f1b1588baea4805bf5'))
g79=pin('research/ordinary14-natural-forced-w79-lean-draft/P79NaturalForcedW.lean','5542e9c16d57619c8b1d6c2c13b870abff4ee9b90307280633fabefc98955d36')
g80=pin('research/ordinary14-natural-forced-gamma80-lean-draft/P80NaturalForcedGamma.lean','015214c4176ab1600c573297521b43987eb66fe863d918a6bcff803a76ca44d9')
model=pin('Lean/DiophantineConsistency/ModelDifferenceRing.lean','5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998')
assert len(a['source'])==79 and len(b['source'])==80 and a['witnesses']==b['witnesses'] and a['witnesses'][6]=='n_w'
assert a['fixed_numerals']==b['fixed_numerals'] and ['w','+','n_w',1] in b['source']
assert a['source']==[[n,op,'n_w' if x=='w' else x,'n_w' if y=='w' else y] for n,op,x,y in b['source'] if n!='w']
assert g80.count('  let w := n_w + 1\n')==1 and g80.count('  let X := q * w\n')==1
assert g80.replace('P80NaturalForcedGamma','P79NaturalForcedW').replace('  let w := n_w + 1\n','').replace('  let X := q * w\n','  let X := q * n_w\n')==g79
assert 'if j = 6 then v j - 1 else v j' in s and 'v79 6 = v80 6 + 1' in s
assert '(positive_w : ∀ v, InternalZero (P79NaturalForcedW.graph p).output v → 0 < v 6)' in s
assert 'simpa [w, add_comm] using hz' in s
assert '(internalZero_iff_related p hw).mp hv' in s and '(internalZero_iff_related p (related_lift w)).mpr hw' in s
assert 'theorem internalZero_iff' in model
for n in ('output_eval','internalZero_iff_related','exists_zero_iff_of_positive'):
 assert '#print axioms DiophantineConsistency.Natural79WShiftDraft.'+n in s
print(json.dumps({'scope':'exact graph edit and proposed model source signatures; no Lean or iPRA proof','pinned_files':6,'removed_gate':'w=n_w+1','shifted_slot':6,'positive_w_explicit_premise':True,'axiom_reports_not_run':3},sort_keys=True,indent=2))
