import DiophantineConsistency.CurrentControllerSubsets2011
import DiophantineConsistency.CurrentControllerPositions2011
import DiophantineConsistency.CurrentControllerUnits2011

/-! Every controller target has an actual finite support of safe physical
cells. The complete power sum and its Gamma-weighted version are derived;
no orbit, subset, safe-set, or unit hypothesis is supplied. Actual digit
mutation and ordinary rank realization are separate constructions. -/
namespace DiophantineConsistency.CurrentSafeController2011

open CurrentControllerData2011 CurrentControllerSubsets2011
  CurrentControllerPositions2011 CurrentControllerUnits2011
open scoped BigOperators
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

attribute [local irreducible] CurrentControllerData2011.B
  CurrentKernel2011.K CurrentControllerUnits2011.Gamma

/-- The natural support contains each selected orbit position once and
adds the distinct position3 exactly when the Boolean coefficient is1. -/
theorem support_power_sum {R : Type*} [CommSemiring R] (b : R)
    (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε : ℕ) (hε : ε ≤ 1) :
    (∑ n ∈ support k s ε, b^n) =
      (∑ j ∈ s, b^(2+(auxiliary-1)*j.val))+(ε : R)*b^3 := by
  unfold support
  split_ifs with h
  · rw [Finset.sum_image (position_injective k).injOn,h,Nat.cast_zero,zero_mul,add_zero]
    rfl
  · have he : ε = 1 := by omega
    rw [Finset.sum_insert (three_not_mem_image k s),
      Finset.sum_image (position_injective k).injOn,he,Nat.cast_one,one_mul]
    exact add_comm _ _

/-- Canonical cyclic values equal the proved natural positions, so the
whole support power sum is unchanged on passing to ZMod N. -/
theorem cyclicSupport_power_sum {R : Type*} [CommSemiring R] (b : R)
    (k : ℕ) (s : Finset (ZMod (auxiliary^k))) (ε : ℕ) (hε : ε ≤ 1) :
    (∑ j ∈ cyclicSupport k s ε, b^j.val) =
      (∑ j ∈ s, b^(2+(auxiliary-1)*j.val))+(ε : R)*b^3 := by
  rw [cyclicSupport,Finset.sum_image (support_cast_injective k s ε)]
  calc
    (∑ n ∈ support k s ε, b^((n : ZMod (auxiliary^(k+1))).val)) =
        ∑ n ∈ support k s ε, b^n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hl : n < auxiliary^(k+1) := by
        have h := (support_basic k s ε n hn).2
        omega
      rw [ZMod.val_natCast_of_lt hl]
    _ = _ := support_power_sum b k s ε hε

/-- Construct an actual nonempty safe physical support for every target.
The quantitative upper cardinality bound includes the optional cell3. -/
theorem exists_safe_power_sum (k rw : ℕ) (hrw : rw < k)
    (hlarge : d*auxiliary < auxiliary^k) (t : ZMod (d*auxiliary^(k+1))) :
    ∃ S : Finset (ZMod (auxiliary^(k+1))),
      0 < S.card ∧ S.card ≤ d*auxiliary ∧
      (∀ j ∈ S, 0 < j.val ∧ j.val+1 < auxiliary^(k+1) ∧
        j.val+auxiliary^rw < auxiliary^(k+1)) ∧
      (∑ j ∈ S, (B : ZMod (d*auxiliary^(k+1)))^j.val) = t := by
  obtain ⟨ε,a,s,hε,hapos,ha,hcard,hs⟩ := exists_shifted_subset k hlarge t
  have hc : (cyclicSupport k s ε).card = a+ε := by
    rw [cyclicSupport_card k s ε hε,hcard]
  refine ⟨cyclicSupport k s ε,by omega,by omega,?_,?_⟩
  · intro j hj
    exact cyclicSupport_safe hrw s ε j hj
  · exact (cyclicSupport_power_sum _ k s ε hε).trans hs

/-- The literal Gamma is already proved a unit at this entire modulus.
An inverse-normalized target therefore gives a safe support for Gamma times
the power sum, without any unit or prescribed-support premise. -/
theorem exists_safe_gamma_sum (k rw : ℕ) (hrw : rw < k)
    (hlarge : d*auxiliary < auxiliary^k) (t : ZMod (d*auxiliary^(k+1))) :
    ∃ S : Finset (ZMod (auxiliary^(k+1))),
      0 < S.card ∧ S.card ≤ d*auxiliary ∧
      (∀ j ∈ S, 0 < j.val ∧ j.val+1 < auxiliary^(k+1) ∧
        j.val+auxiliary^rw < auxiliary^(k+1)) ∧
      (Gamma rw (k+1) : ZMod (d*auxiliary^(k+1)))*
        (∑ j ∈ S, (B : ZMod (d*auxiliary^(k+1)))^j.val) = t := by
  have hu : IsUnit (Gamma rw (k+1) : ZMod (d*auxiliary^(k+1))) :=
    isUnit_Gamma_width_cells rw (k+1)
  obtain ⟨v,hv⟩ := hu.exists_right_inv
  obtain ⟨S,hpos,hcard,hsafe,hsum⟩ := exists_safe_power_sum k rw hrw hlarge (v*t)
  refine ⟨S,hpos,hcard,hsafe,?_⟩
  rw [hsum,← mul_assoc,hv,one_mul]

end DiophantineConsistency.CurrentSafeController2011
