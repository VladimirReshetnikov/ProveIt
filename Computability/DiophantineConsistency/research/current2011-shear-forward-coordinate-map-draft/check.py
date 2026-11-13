#!/usr/bin/env python3
"""Read-only direct-source pins and markers; no Lean invocation."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-forward-coordinate-map-draft/ForwardCoordinateMap.lean.src':'05bb78857a208caa5cfec1dfe78ccda68b6aa4f552db62adf271faff5384a9c6',
 'research/current2011-sheared72-literal-evaluator-draft/Shear72Literal.lean.src':'5f06d64754d71f75b7fef0a9a046c1de9656c9f94e1f36f968c3b81a915a8739',
 'research/current2011-shear-positive-gap-representation-draft/PositiveGapRepresentation.lean.src':'330544ffaedd3afc061931ace2b0518f3ebd5b855e56516944cc34322033b049',
 'research/current2011-shear-current-port-cast-draft/CurrentPortCast.lean.src':'be27b59b37e99d41eb90f6913ef6f19f0d943581c51ded85477477e9f46fc320',
 'research/current2011-shear-forward-norm-order-draft/ForwardNormOrder.lean.src':'de67ebbb8699e8f43f28f8db6caca0da8edaed522503e4ba9a98f4d12b7a5b2d',
 'research/current2011-shear-forward-index-binding-draft/ForwardIndex.lean.src':'fb39f3cb211700acd7e431da2f7a4e95a256a4a6f98087f8db0cb163beb9101a',
}
for path,h in PINS.items():
 if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=h: raise RuntimeError('pin changed: '+path)
src=(ROOT/'research/current2011-shear-forward-coordinate-map-draft/ForwardCoordinateMap.lean.src').read_text()
for token in ['theorem V_update_y','theorem shear_inverse','Function.update u 12 x',
              'theorem shifted_child_eq_update','ι (n+1)','theorem forward_zero_of_rep',
              'theorem forward_zero','ring_half_at_parent_zero','literal_positive_shear',
              'positive_gap_as_successor','forward_zero_of_rep v n hn hz']:
 if token not in src: raise RuntimeError('missing marker: '+token)
print(json.dumps({'scope':'direct source pins and coordinate markers only; no Lean elaboration',
 'pinned_drafts':len(PINS),'coordinate':12,'natural_shift':'n+1',
 'complete_forward_theorem_is_proposed_only':True},indent=2,sort_keys=True))
