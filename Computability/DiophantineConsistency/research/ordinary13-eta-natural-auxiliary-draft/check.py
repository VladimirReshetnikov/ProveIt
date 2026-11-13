#!/usr/bin/env python3
"""Pin the fact providers and proposed composition, without invoking Lean."""
from pathlib import Path
import hashlib,json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
here=Path(__file__).resolve().parent;root=here.parents[1]
pins={
'research/ordinary14-aux-geometry-model-draft/AuxGeometry.lean':'88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77',
'research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean':'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504',
'research/ordinary14-aux-root-model-draft/AuxRootBridge.lean':'796819c48d53665e1ee9c90d8d1bfd0fbd00cd4ca5535fe4fad1a3462d74c8b7',
'Lean/DiophantineConsistency/ModelDifferenceRing.lean':'5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
def readpin(p,h):
 b=(root/p).read_bytes();assert hashlib.sha256(b).hexdigest()==h,p;return b.decode()
s={p:readpin(p,h) for p,h in pins.items()}
r=s['research/ordinary14-aux-root-bounds-model-draft/AuxRootBounds.lean']
for term in ('theorem first_ordinate_large','theorem strong_f_square_large','theorem strong_Q_gt_one','theorem signed_square_gt_one'):assert term in r
r=s['research/ordinary14-aux-root-model-draft/AuxRootBridge.lean']
for term in ('theorem square_gt_of_aux','theorem above_of_positive'):assert term in r
b=(here/'AuxOffsetFacts.lean.src').read_bytes();text=b.decode()
for term in ('theorem aux_strict_bounds','theorem positive_offset_of_direct','strong_f_square_large','strong_Q_gt_one','signed_square_gt_one','square_gt_of_aux','above_of_positive','ι_nonneg y'):assert term in text
assert 'sorry' not in text and '\naxiom ' not in text
print(json.dumps({'source_sha256':pins,'client_sha256':hashlib.sha256(b).hexdigest(),'scope':'bounded lexical source-interface receipt; no elaboration or graph binding','lean_elaborated':False},sort_keys=True,indent=2))
