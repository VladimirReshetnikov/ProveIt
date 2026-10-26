import DiophantineConsistency.CurrentSafeController2011

namespace DiophantineConsistency.CurrentSafeController2011Checks

open CurrentControllerData2011 CurrentControllerPositions2011
  CurrentControllerUnits2011 CurrentSafeController2011
open scoped BigOperators
set_option Elab.async false
attribute [local irreducible] CurrentControllerData2011.B
  CurrentKernel2011.K CurrentControllerUnits2011.Gamma

-- Both optional-bit values are checked over an arbitrary coefficient ring.
example {R : Type*} [CommSemiring R] (b : R) (k : ℕ) :
    (∑ j ∈ cyclicSupport k ∅ 0, b^j.val) = 0 := by
  simpa only [Finset.sum_empty,Nat.cast_zero,zero_mul,add_zero] using
    cyclicSupport_power_sum b k ∅ 0 (by decide)
example {R : Type*} [CommSemiring R] (b : R) (k : ℕ) :
    (∑ j ∈ cyclicSupport k ∅ 1, b^j.val) = b^3 := by
  simpa only [Finset.sum_empty,Nat.cast_one,one_mul,zero_add] using
    cyclicSupport_power_sum b k ∅ 1 (by decide)

-- Orbit index0 and optional3 are separate cells with powers b² and b³.
example {R : Type*} [CommSemiring R] (b : R) (k : ℕ) :
    (∑ j ∈ cyclicSupport k {0} 1, b^j.val) = b^2+b^3 := by
  simpa only [Finset.sum_singleton,ZMod.val_zero,Nat.mul_zero,Nat.add_zero,
    Nat.cast_one,one_mul] using cyclicSupport_power_sum b k {0} 1 (by decide)

-- A concrete admissible pair of exponents also covers target zero.
example : ∃ S : Finset (ZMod (auxiliary^(2+1))),
    0 < S.card ∧ S.card ≤ d*auxiliary ∧
    (∀ j ∈ S, 0 < j.val ∧ j.val+1 < auxiliary^(2+1) ∧
      j.val+auxiliary^1 < auxiliary^(2+1)) ∧
    (Gamma 1 (2+1) : ZMod (d*auxiliary^(2+1)))*
      (∑ j ∈ S, (B : ZMod (d*auxiliary^(2+1)))^j.val) = 0 :=
  exists_safe_gamma_sum 2 1 (by decide) (by decide) 0

-- All safe-set and unit facts are conclusions or proved dependencies.
example (k rw : ℕ) (hrw : rw < k) (hlarge : d*auxiliary < auxiliary^k)
    (t : ZMod (d*auxiliary^(k+1))) :
    ∃ S : Finset (ZMod (auxiliary^(k+1))),
      0 < S.card ∧ S.card ≤ d*auxiliary ∧
      (∀ j ∈ S, 0 < j.val ∧ j.val+1 < auxiliary^(k+1) ∧
        j.val+auxiliary^rw < auxiliary^(k+1)) ∧
      (Gamma rw (k+1) : ZMod (d*auxiliary^(k+1)))*
        (∑ j ∈ S, (B : ZMod (d*auxiliary^(k+1)))^j.val) = t :=
  exists_safe_gamma_sum k rw hrw hlarge t

#print axioms support_power_sum
#print axioms cyclicSupport_power_sum
#print axioms exists_safe_power_sum
#print axioms exists_safe_gamma_sum

end DiophantineConsistency.CurrentSafeController2011Checks
