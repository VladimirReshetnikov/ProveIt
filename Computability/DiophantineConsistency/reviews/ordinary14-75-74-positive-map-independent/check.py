#!/usr/bin/env python3
"""Independent source interface and exact coordinate controls; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys
P=Path(__file__).resolve().parent;D=P.parents[1];A=D/'research/ordinary14-75-74-positive-map-draft'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins={'README.md':'f4ddf3eada25751f70cd62a48aa2e5cab93f9df8bbabcd3287af1a3f9fde4486','Positive75To74.lean':'c8e10e66643f025988751af1a55b7d70dc23ea25eec70b6efe4dc256003b7d70','check_source.py':'117f5abad70c05adcf76ed858714302d04b0a907b05f828285cea2eec4f79029','observation.json':'f85c1bf9f75db3f8c82ea853aad4658c06a835ae9f2fc231f97eaeba2c96d9e8'}
tail=b"\nIndependent source review: [75/74 positive maps](../../reviews/ordinary14-75-74-positive-map-independent/README.md).\n"
final=(A/'README.md').read_bytes()
assert hashlib.sha256(final).hexdigest()=='0c76c77eb64d1c5d8d8cc26b1f3347dee976d4501ed08c08bf4ed8423efafbbd'
assert final.endswith(tail) and hashlib.sha256(final[:-len(tail)]).hexdigest()==pins['README.md']
for n,h in pins.items():
 if n!='README.md':assert sha(A/n)==h,n
s=(A/'Positive75To74.lean').read_text(); ring=D/'research/ordinary14-75-74-ring-client-draft/Ring75To74.lean';rs=ring.read_text();root=D/'Lean/DiophantineConsistency/Compact44/P72Root.lean';roots=root.read_text()
assert sha(ring)=='50f5b856f5c9fc379c035d91dc19e4b97c9234feed3918785f66900d69a049b6'
assert sha(root)=='066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091'
assert re.search(r'theorem ι_tsub\s*\{a b : V\}\s*\(h : b ≤ a\)\s*:\s*ι \(a - b\) = ι a - ι b',roots)
for token in ['Function.update v 13 (v 13+1)','Function.update v 13 (v 13-1)','(hstrict : 1<v 13)','tsub_pos_of_lt hstrict','P72Root.ι_tsub (le_of_lt hstrict)','rw [←cast_forward v] at h','rw [←cast_reverse v hstrict] at h','rw [←h]','(internalZero_iff _ _).mp hz']:
 assert token in s,token
assert not re.search(r'\b(?:sorry|admit|axiom)\b',s)
assert 'Function.update v 13 (v 13+1)' in rs and 'theorem output_eval' in rs
# Independently instantiate both coordinate directions; strictness is needed at h=1.
cases=0
for h in range(1,201):
 v=tuple(range(1,15));old=v[:13]+(h,);new=old[:13]+(h+1,)
 assert all(a>0 for a in new) and new[:13]==old[:13] and new[13]-1==old[13]
 assert new[13]>1
 cases+=1
assert (1-1)==0
# Ring guard identity is valid with arbitrary signed operands, not just positive witnesses.
ring_controls=0
for C in range(-2,3):
 for X in range(-2,3):
  for K in range(-1,2):
   for F in range(-1,2):
    for b in range(-1,2):
     for h in range(-1,2):
      assert C*(X+K)+(1+b-F)-b*(h+1)==1+(C*(X+K)-F-b*h)
      ring_controls+=1
review=D/'reviews/ordinary14-unit75-guard74-lean-independent'
assert sha(review/'check.py')=='b153758cd7367e0bf29edb09d14ccd68aaa0d3a8be6ced73d6d8db39d45fc416'
assert sha(review/'observation.json')=='d45f47278ca59002644d3d02255e8813cde83f13424f698f4670c01c11ab4ee5'
assert subprocess.run([sys.executable,'-I','-S','-B',str(review/'check.py')],cwd=D,check=True,capture_output=True).stdout==(review/'observation.json').read_bytes()
receipt=subprocess.run([sys.executable,'-I','-S','-B',str(A/'check_source.py')],cwd=D,check=True,capture_output=True).stdout
assert receipt==(A/'observation.json').read_bytes()
print(json.dumps({'scope':'source interface and finite coordinate checks only; no Lean, unconditional reverse, provider or endpoint','author_pins':pins,'ring_source_sha256':sha(ring),'p72root_sha256':sha(root),'positive_coordinate_controls':cases,'signed_ring_guard_controls':ring_controls,'independent_graph_review_replayed':True,'h_equal_one_reverse_not_positive':True,'author_receipt_reproduced':True},sort_keys=True,indent=2))
