#!/usr/bin/env python3
"""Generate a closed byte recipe from the pinned parent payload, externally."""
from hashlib import sha256
from pathlib import Path
import gzip
import json

here = Path(__file__).resolve().parent
root = here.parents[4]
payload = root / ('Computability/DiophantineConsistency/candidates/'
                  'free-j-polarized-positive/source/positive/coefficients/payloads/MC.bin.gz')
gz = payload.read_bytes()
assert sha256(gz).hexdigest() == '271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e'
raw = gzip.decompress(gz)
assert sha256(raw).hexdigest() == '6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4'
assert len(raw) == 73759
dense = [(17,7890), (8233,8308), (8401,8468), (8484,8635)]
gaps = [(7898,8225), (8317,8392), (8643,8895), (8920,9163),
        (9179,18375), (18392,27596)]
covered = [(0,16), (27613,73751)] + dense + gaps
indices = set().union(*(range(lo,hi) for lo,hi in covered))
assert len(indices) == sum(hi-lo for lo,hi in covered) == 73617
remaining = [i for i in range(len(raw)) if i not in indices]
exceptions = [(i,raw[i]) for i in remaining if raw[i] != 255]
assert len(remaining) == 142 and len(exceptions) == 11

def dense_value(j):
    r = 8*j%67
    return 254 if r == 0 else 255-2**(67-r) if r >= 60 else 255

def value(j):
    if j == 0:
        return 254
    if any(lo <= j < hi for lo,hi in dense):
        return dense_value(j)
    return dict(exceptions).get(j,255)

assert all(value(i) == b for i,b in enumerate(raw))
assert payload.read_bytes() == gz
clauses = '\n'.join(f'  if j = {i} then {v} else' for i,v in exceptions)
source = f'''import Mathlib.Data.Nat.Digits.Lemmas

/-! Generated closed byte recipe; file provenance remains external. -/
set_option autoImplicit false
namespace CompactLowByteRecipeData

def denseWindow (r : ℕ) : ℕ :=
  if r = 0 then 254 else if 60 ≤ r then 255 - 2^(67-r) else 255

def irregularByte (j : ℕ) : ℕ :=
{clauses}
  255

def denseIndex (j : ℕ) : Prop :=
  (17 ≤ j ∧ j < 7890) ∨ (8233 ≤ j ∧ j < 8308) ∨
  (8401 ≤ j ∧ j < 8468) ∨ (8484 ≤ j ∧ j < 8635)

instance (j : ℕ) : Decidable (denseIndex j) := by unfold denseIndex; infer_instance

def byteAt (j : ℕ) : ℕ :=
  if j = 0 then 254 else if denseIndex j then denseWindow ((8*j)%67)
  else irregularByte j

def bytes : List ℕ := (List.range 73759).map byteAt

theorem bytes_length : bytes.length = 73759 := by simp [bytes]

theorem bytes_getD (j : ℕ) (hj : j < 73759) : bytes.getD j 0 = byteAt j := by
  unfold bytes
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp

#print axioms CompactLowByteRecipeData.bytes_getD
end CompactLowByteRecipeData
'''
out = here/'CompactLowByteRecipeData.lean'
out.write_text(source)
print(json.dumps({'raw_sha256': sha256(raw).hexdigest(), 'raw_bytes': len(raw),
                  'dense_intervals': dense, 'remaining_indices': len(remaining),
                  'exceptions': exceptions, 'source_sha256': sha256(source.encode()).hexdigest(),
                  'whole_payload_matches': True}, indent=2, sort_keys=True))
