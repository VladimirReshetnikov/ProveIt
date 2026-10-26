import DiophantineConsistency.ControllerIntervalSums

namespace DiophantineConsistency.ControllerIntervalSumsChecks

open ControllerIntervalSums
open scoped BigOperators

set_option Elab.async false
set_option maxRecDepth 10000

-- Actual wrap: the three distinct coordinates are4,0,1, and sum to0.
example : interval (4 : ZMod 5) 3 = {4,0,1} ∧
    (interval (4 : ZMod 5) 3).card = 3 ∧
    (∑ z ∈ interval (4 : ZMod 5) 3, z) = 0 := by decide

-- The explicit unit-based start reaches2 with the wrapping interval3,4,0.
example : startFor 3 (by decide : Nat.Coprime 3 5) (2 : ZMod 5) = 3 ∧
    targetInterval 3 (by decide : Nat.Coprime 3 5) (2 : ZMod 5) = {3,4,0} := by
  have he := startFor_equation 3 (by decide : Nat.Coprime 3 5) (2 : ZMod 5)
  change (3 : ZMod 5)*startFor 3 (by decide) 2+3 = 2 at he
  have hc : (3 : ZMod 5)*3+3 = 2 := by decide
  have hm := add_right_cancel (he.trans hc.symm)
  have hu := (ZMod.isUnit_iff_coprime 3 5).mpr (by decide)
  have hs := hu.mul_right_inj.mp hm
  refine ⟨hs,?_⟩
  rw [targetInterval,hs]
  decide

example {T : ℕ} [NeZero T] (start : ZMod T) :
    (interval start 0).card = 0 ∧ (∑ z ∈ interval start 0, z) = 0 := by
  simp [interval]

-- A full interval has the entire modulus as its cardinality, including wrap.
example (start : ZMod 4) : (interval start 4).card = 4 ∧
    (∑ z ∈ interval start 4, z) = 2 := by
  refine ⟨interval_card start 4 (by omega),?_⟩
  rw [interval_sum start 4 (by omega)]
  rw [ZMod.natCast_self,zero_mul,zero_add]
  decide

-- Division is performed in Nat. Dividing the cast numerator by2 in ZMod4
-- would produce0 here, whereas the correct triangular sum is2.
example : (((4*(4-1)/2 : ℕ) : ZMod 4)) = 2 ∧
    ((4*(4-1) : ZMod 4) * (2 : ZMod 4)⁻¹) = 0 := by
  constructor
  · decide
  · rw [show (4 : ZMod 4) = 0 by decide,zero_mul,zero_mul]

-- A=0 is coprime toT=1, and the empty subset reaches its sole target.
example (u : ZMod 1) :
    (targetInterval 0 (by decide : Nat.Coprime 0 1) u).card = 0 ∧
      (∑ z ∈ targetInterval 0 (by decide : Nat.Coprime 0 1) u, z) = u :=
  ⟨targetInterval_card 0 (by decide) (by decide) u,
    targetInterval_sum 0 (by decide) (by decide) u⟩

-- The other endpoint a=T=1 gives the singleton rather than the empty subset.
example (u : ZMod 1) :
    (targetInterval 1 (by decide : Nat.Coprime 1 1) u).card = 1 ∧
      (∑ z ∈ targetInterval 1 (by decide : Nat.Coprime 1 1) u, z) = u :=
  ⟨targetInterval_card 1 (by decide) (by decide) u,
    targetInterval_sum 1 (by decide) (by decide) u⟩

-- The length bound prevents image collisions; exceedingT loses cardinality.
example : (interval (0 : ZMod 3) 4).card = 3 ∧
    (interval (0 : ZMod 3) 4).card ≠ 4 := by decide

-- Without coprimality, consecutive intervals need not reach every target.
-- This is an interval obstruction, not an obstruction for arbitrary subsets.
example : ¬ Nat.Coprime 2 4 ∧
    ¬ ∃ start : ZMod 4, (∑ z ∈ interval start 2, z) = 0 := by decide

example : ({1,3} : Finset (ZMod 4)).card = 2 ∧
    (∑ z ∈ ({1,3} : Finset (ZMod 4)), z) = 0 := by decide

-- No supplied subset witness occurs in the full symbolic endpoint.
example {T : ℕ} [NeZero T] (a : ℕ) (h : Nat.Coprime a T)
    (ha : a ≤ T) (u : ZMod T) :
    ∃ s : Finset (ZMod T), s.card = a ∧ (∑ z ∈ s, z) = u :=
  exists_subset_card_sum a h ha u

#print axioms interval_injOn
#print axioms interval_card
#print axioms interval_sum
#print axioms startFor_equation
#print axioms targetInterval_card
#print axioms targetInterval_sum
#print axioms exists_interval_sum
#print axioms exists_subset_card_sum

end DiophantineConsistency.ControllerIntervalSumsChecks
