#!/usr/bin/env python3
"""Static source and literal-row checks; no Lean execution."""
import hashlib
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
PINS={
 'research/current2011-shear-reverse-coordinate-map-draft/ReverseCoordinateMap.lean.src':'0b785082d608ff55397d1624f777a4775a6555702dae6ab504fb3c58a2cb84e3',
 'research/current2011-shear72-reverse-graph-bounds-draft/Shear72ReverseGraphBounds.lean.src':'51ee53129e01054cc78c83c5f74022dce8fd67d11d34971e5093f4199a845159',
 'research/current2011-sheared72-literal-evaluator-draft/Shear72Literal.lean.src':'5f06d64754d71f75b7fef0a9a046c1de9656c9f94e1f36f968c3b81a915a8739',
 'research/current2011-ordinary71-60-literal/OrdinarySphere7160Literal.lean':'554fa13261dcb4f9535764871b4833d0b6182fab9503bfa27b3bc5f88d64d84a',
 'research/normalized106-fresh-base-model-build/FreshModel106.lean':'61e64a2ef559c3da369021df2705cd76f957bc0ea971467b80d627eaa9422769',
 'research/current2011-ordinary71-60-candidate/polynomial.json':'3c50ef12124daab13a6f67e03e273ecc91a5bed2fd3557a1343514b3b4171e27',
}
for path,h in PINS.items():
 if hashlib.sha256((ROOT/path).read_bytes()).hexdigest()!=h: raise RuntimeError('pin changed: '+path)
parent=json.loads((ROOT/'research/current2011-ordinary71-60-candidate/polynomial.json').read_bytes())
uses=[r for r in parent['source'] if 'y' in r[2:]]
if uses!=[['y2','*','y','y']]: raise RuntimeError('parent ordinate has another direct use')
src=(ROOT/'research/current2011-shear-reverse-coordinate-map-draft/ReverseCoordinateMap.lean.src').read_text()
for marker in ['theorem parent_eval_update_same_square','theorem shifted_parent_eq_update',
 'Function.update v 12 (m-1)','theorem reverse_zero_of_magnitude','theorem reverse_zero',
 'candidate_zero_positive_ordinate','FreshModel106.beta_pos','Shear72LiteralDraft.eval_eq_sheared71']:
 if marker not in src: raise RuntimeError('missing source marker: '+marker)
print(json.dumps({'scope':'source pins and literal y-row only; draft unelaborated',
 'pinned_files':len(PINS),'coordinate':12,'natural_shift':'(m−1)+1=m',
 'parent_direct_y_uses':uses,'complete_reverse_theorem_is_proposed_only':True},indent=2,sort_keys=True))
