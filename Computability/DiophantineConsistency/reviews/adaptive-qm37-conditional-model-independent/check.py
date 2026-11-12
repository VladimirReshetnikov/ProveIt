#!/usr/bin/env python3
"""Independent, read-only coordinate and premise audit; no Lean."""
from pathlib import Path
import hashlib,json,re,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path(__file__).resolve().parents[2]
def pin(path,h):
 b=(D/path).read_bytes(); assert hashlib.sha256(b).hexdigest()==h,path; return b.decode()
pre='research/adaptive-qm37-conditional-model-draft/'
t=pin(pre+'AdaptiveQM37ConditionalTransfer.lean.src','be810ba3342ba05423e42e70eceff065809ba0380b804b79060b17ae73415566')
w=pin(pre+'AdaptiveQM37DifferenceWitness.lean.src','b65647fb73619d6f52e166ae61233854a47e9f968174481f321f44bcdf915c80')
pin(pre+'result.json','fc2e96e8ad44be18f0653f7667241a91fa441f39bec1bf41cd1356d371dbb680')
pin('reviews/adaptive-square-sums37-independent/result.json','58ba07591199a0ce77fa6c6863390e3f7b72894c0f6d564d41cdc3e86567094c')
parent=json.loads(pin('research/adaptive-square-sums38-two-quadratic-products/candidate.json','ee523a8a821df163b038a19c4902234d3f09e730cbeee255dd4c896bdff7ae56'))
child=json.loads(pin('research/adaptive-square-sums37-difference-quartic/candidate.json','b79e1a1fe708c7ba9a7406c8c534268d5b7e79128d8402c58637e16e5c462aea'))
assert [parent['witnesses'][i] for i in (11,13,25,30,31)]==['y','squareVariable','vValueVariable','ySquareVariable','qValueVariable']
assert child['witnesses'][13]=='differencePlusOne' and child['witnesses'][30]=='qValueVariable'
for i,n in enumerate(child['witnesses']):
 if i!=13: assert n==parent['witnesses'][i if i<30 else i+1]
for s in ['if i.val=13 then d+1','else if h : i.val<30 then v ⟨i.val, by omega⟩','else v ⟨i.val+1, by omega⟩','if i.val=13 then v 25*v 25','else if i.val=30 then v 11*v 11','else v ⟨i.val-1, by omega⟩','AdaptiveQM37DifferenceWitnessDraft.parent_difference','(h38 : AdaptiveQM38ConditionalTransferDraft.ZeroPreservationObligations)','(h37 : GraphZeroObligations)']:
 assert s in t,s
for s in ['have hs := h 4','have hy := h 21','.mp hz 2','v 31*(v 11*v 11)+1 = v 31*(v 25*v 25)+v 11*v 11','(hq : 0<q) (hy : 0<y)','by_contra hn','mul_lt_mul_of_pos_left hlt hq','exists_add_of_le hle','(hv 31) (hv 11)']:
 assert s in w,s
assert not re.search(r'(?m)^\s*(?:sorry|axiom)\b',t+'\n'+w)
# Check contradiction chain and projection/extension identities on all small integer controls.
checks=0
for q in range(1,5):
 for y in range(1,5):
  for z in range(5):
   if q*y*y+1==q*z*z+y*y:
    assert y*y>=z*z
    d=y*y-z*z
    old=list(range(1,39));old[11]=y;old[13]=z*z;old[25]=z;old[30]=y*y;old[31]=q
    proj=[d+1 if i==13 else old[i if i<30 else i+1] for i in range(37)]
    ext=[proj[25]**2 if i==13 else proj[11]**2 if i==30 else proj[i if i<30 else i-1] for i in range(38)]
    assert ext==old and proj[13]>0
    checks+=1
print(json.dumps({'scope':'static source and finite controls; no Lean elaboration or iPRA proof','child_coordinates_checked':37,'parent_coordinates_checked':38,'ordered_model_conditions':'positive q and y; additive square difference; project and extend zero obligations','finite_aux_witness_cases':checks,'prior_qm38_obligation_remains_explicit':True},sort_keys=True,indent=2))
