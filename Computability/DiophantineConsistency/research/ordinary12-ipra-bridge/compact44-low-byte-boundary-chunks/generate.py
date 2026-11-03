#!/usr/bin/env python3
"""Generate separately bounded Lean sources for the 142 boundary windows."""
from hashlib import sha256
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
INTERVALS = [(16,17), (7890,7898), (8225,8233), (8308,8317),
             (8392,8401), (8468,8484), (8635,8643), (8895,8920),
             (9163,9179), (18375,18392), (27596,27613), (73751,73759)]
assert sum(hi-lo for lo,hi in INTERVALS) == 142
rows=[]
for n,(lo,hi) in enumerate(INTERVALS,1):
    name=f'CompactLowByteBoundary{n:02d}'
    source=f'''import CompactLowByteRecipeData
import CompactLowByteWindow

/-! Finite symbolic byte-window certificate for [{lo},{hi}). -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace {name}

theorem windows (j : ℕ) (hlo : {lo} ≤ j) (hhi : j < {hi}) :
    CompactLowByteRecipeData.byteAt j = (CompactSymbolicPorts.lowNat / 256^j) % 256 := by
  have hp : (256:ℕ)^j = 2^(8*j) := by
    rw [show (256:ℕ) = 2^8 by norm_num, ← pow_mul]
  rw [hp, CompactLowByteWindow.low_byte]
  interval_cases j <;>
    norm_num [CompactLowByteRecipeData.byteAt, CompactLowByteRecipeData.denseIndex,
      CompactLowByteRecipeData.irregularByte, CompactLowByteWindow.padded_digit,
      CompactListMask.digit, CompactConcreteMask.support]

#print axioms {name}.windows
end {name}
'''
    (HERE/(name+'.lean')).write_text(source)
    rows.append({'module':name,'lower':lo,'upper_exclusive':hi,'count':hi-lo,
                 'source_sha256':sha256(source.encode()).hexdigest()})
print(json.dumps({'intervals':rows,'count':sum(x['count'] for x in rows)},indent=2,sort_keys=True))
