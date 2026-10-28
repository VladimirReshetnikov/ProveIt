import DiophantineConsistency.CurrentPowerCoordinates2011

/-!
# Actual Boolean power subsets for the current controller

The coordinate equivalence, the optional Boolean term, the positive small
cardinality, and the subset are all constructed from the checked current
constants. The final statement includes the B² normalization and the whole
modulus d * auxiliary^(k+1). Physical placement and the rank factor Gamma
are deliberately separate: neither is a premise or conclusion here.
-/

namespace DiophantineConsistency.CurrentControllerSubsets2011

open CurrentControllerData2011 CurrentPowerCoordinates2011
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

attribute [local irreducible] CurrentControllerData2011.B

/-- The actual B is a power of two and the entire block modulus is odd. -/
theorem block_base_isUnit (k : ℕ) :
    IsUnit (B : ZMod ((d*auxiliary)*auxiliary^k)) := by
  rw [B_eq, Nat.cast_pow]
  exact ((ZMod.isUnit_iff_coprime 2 _).mpr (Nat.coprime_two_left.mpr
    ((d_odd.mul auxiliary_odd).mul auxiliary_odd.pow))).pow 94517

/-- All normalized targets have a genuine subset of actual power indices.
No orbit equivalence, affine-weight identity or subset is supplied. -/
theorem exists_normalized_subset (k : ℕ) (hlarge : d*auxiliary < auxiliary^k)
    (t : ZMod ((d*auxiliary)*auxiliary^k)) :
    ∃ ε a : ℕ, ∃ s : Finset (ZMod (auxiliary^k)),
      ε ≤ 1 ∧ 0 < a ∧ a < d*auxiliary ∧ s.card = a ∧
      (∑ j ∈ s, (B : ZMod ((d*auxiliary)*auxiliary^k))^
        ((auxiliary-1)*j.val))+
        (ε : ZMod ((d*auxiliary)*auxiliary^k))*B = t := by
  letI : NeZero (d*auxiliary) := ⟨by decide⟩
  obtain ⟨e,he⟩ := exists_base_power_coordinates k
  apply ControllerResidueLift.exists_subset_boolean_sum prime_auxiliary
    (dvd_mul_left auxiliary d) k rfl hlarge e e.injective
    (fun j => (B : ZMod ((d*auxiliary)*auxiliary^k))^((auxiliary-1)*j.val))
    he t (B : ZMod ((d*auxiliary)*auxiliary^k))
  rw [map_natCast, map_natCast, B_cast_auxiliary]
  decide

/-- Multiplying by B² shifts every orbit exponent and the Boolean term. -/
private theorem shifted_sum {R : Type*} [CommSemiring R]
    {α : Type*} [DecidableEq α] (b : R) (f : α → ℕ)
    (s : Finset α) (ε : ℕ) :
    (∑ j ∈ s, b^(2+f j))+(ε : R)*b^3 =
      b^2*((∑ j ∈ s, b^(f j))+(ε : R)*b) := by
  rw [mul_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    exact pow_add b 2 (f j)
  · ring

/-- Every target is realized after the required B² normalization. -/
theorem exists_shifted_subset_block (k : ℕ) (hlarge : d*auxiliary < auxiliary^k)
    (t : ZMod ((d*auxiliary)*auxiliary^k)) :
    ∃ ε a : ℕ, ∃ s : Finset (ZMod (auxiliary^k)),
      ε ≤ 1 ∧ 0 < a ∧ a < d*auxiliary ∧ s.card = a ∧
      (∑ j ∈ s, (B : ZMod ((d*auxiliary)*auxiliary^k))^
        (2+(auxiliary-1)*j.val))+
        (ε : ZMod ((d*auxiliary)*auxiliary^k))*(B : ZMod ((d*auxiliary)*auxiliary^k))^3
        = t := by
  obtain ⟨v,hv⟩ := ((block_base_isUnit k).pow 2).exists_right_inv
  obtain ⟨ε,a,s,hε,hapos,ha,hcard,hs⟩ := exists_normalized_subset k hlarge (v*t)
  refine ⟨ε,a,s,hε,hapos,ha,hcard,?_⟩
  rw [shifted_sum, hs, ← mul_assoc, hv, one_mul]

/-- Modulus transport stays opaque in the enormous natural base. -/
private theorem subset_modulus_transport {m n T C0 b κ : ℕ} (hm : m = n)
    (hs : ∀ t : ZMod m, ∃ ε a : ℕ, ∃ s : Finset (ZMod T),
      ε ≤ 1 ∧ 0 < a ∧ a < C0 ∧ s.card = a ∧
      (∑ j ∈ s, (b : ZMod m)^(2+κ*j.val))+(ε : ZMod m)*(b : ZMod m)^3 = t) :
    ∀ t : ZMod n, ∃ ε a : ℕ, ∃ s : Finset (ZMod T),
      ε ≤ 1 ∧ 0 < a ∧ a < C0 ∧ s.card = a ∧
      (∑ j ∈ s, (b : ZMod n)^(2+κ*j.val))+(ε : ZMod n)*(b : ZMod n)^3 = t := by
  subst n
  exact hs

/-- Actual controller subset construction over the entire d*auxiliary^(k+1).
The selected indices are distinct because s is a Finset, and its positive
cardinality is strictly less than C0=d*auxiliary. -/
theorem exists_shifted_subset (k : ℕ) (hlarge : d*auxiliary < auxiliary^k)
    (t : ZMod (d*auxiliary^(k+1))) :
    ∃ ε a : ℕ, ∃ s : Finset (ZMod (auxiliary^k)),
      ε ≤ 1 ∧ 0 < a ∧ a < d*auxiliary ∧ s.card = a ∧
      (∑ j ∈ s, (B : ZMod (d*auxiliary^(k+1)))^(2+(auxiliary-1)*j.val))+
        (ε : ZMod (d*auxiliary^(k+1)))*(B : ZMod (d*auxiliary^(k+1)))^3 = t :=
  subset_modulus_transport (modulus_factorization k)
    (exists_shifted_subset_block k hlarge) t

end DiophantineConsistency.CurrentControllerSubsets2011
