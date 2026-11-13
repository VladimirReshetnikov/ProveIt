import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.List.GetD

/-! Generated closed byte recipe; file provenance remains external. -/
set_option autoImplicit false
namespace CompactLowByteRecipeData

def denseWindow (r : ℕ) : ℕ :=
  if r = 0 then 254 else if 60 ≤ r then 255 - 2^(67-r) else 255

def irregularByte (j : ℕ) : ℕ :=
  if j = 16 then 191 else
  if j = 8232 then 223 else
  if j = 8308 then 254 else
  if j = 8400 then 253 else
  if j = 8483 then 127 else
  if j = 8902 then 159 else
  if j = 8911 then 254 else
  if j = 9170 then 223 else
  if j = 18383 then 253 else
  if j = 27604 then 254 else
  if j = 73758 then 31 else
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
