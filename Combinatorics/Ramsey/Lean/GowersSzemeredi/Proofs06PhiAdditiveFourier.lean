import GowersSzemeredi.Proofs01_03

/-! The fourth moment of `x ↦ 1_B(x)·e(φ(x)·u)`, summed over `u`.

With `prop61G B φ u = 1_B · e(φ·u)`, the fourth moments of the Fourier
transforms count the `φ`-additive quadruples of `B`:
`∑_u ∑_r ‖(prop61G B φ u)^(r)‖⁴ = N²·phiAdditiveCount B φ`
(`prop61_g_fourth_eq_count`). Proposition 6.1 (`Proofs05_10`) and Lemma 13.1
(`Proofs13Basic`) both use it. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

def prop61G {N : Nat} [NeZero N] (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (u x : ZMod N) : Complex :=
  indicator B x * exponential (phi x * u)

abbrev prop61QuadMem {N : Nat} (B : Finset (ZMod N))
    (q : Fin 4 → ZMod N) : Prop :=
  q 0 ∈ B ∧ q 1 ∈ B ∧ q 2 ∈ B ∧ q 3 ∈ B

abbrev prop61AltAdditive {N : Nat} (B : Finset (ZMod N))
    (phi : ZMod N → ZMod N) (q : Fin 4 → ZMod N) : Prop :=
  prop61QuadMem B q ∧ q 0 - q 1 = q 2 - q 3 ∧
    phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)

lemma prop61_alt_count_eq {N : Nat} [NeZero N] (B : Finset (ZMod N))
    (phi : ZMod N → ZMod N) :
    countWhere (prop61AltAdditive B phi) = phiAdditiveCount B phi := by
  unfold countWhere phiAdditiveCount
  refine Finset.card_equiv
    ({ toFun q := ![q 0, q 3, q 2, q 1]
       invFun q := ![q 0, q 3, q 2, q 1]
       left_inv q := by funext i; fin_cases i <;> rfl
       right_inv q := by funext i; fin_cases i <;> rfl } :
      (Fin 4 → ZMod N) ≃ (Fin 4 → ZMod N)) fun q => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, prop61AltAdditive, prop61QuadMem,
    IsPhiAdditive, IsAdditiveQuadruple]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3⟩, hadd, hphi⟩
    exact ⟨fun i => by fin_cases i <;> assumption, sub_eq_sub_iff_add_eq_add.mp hadd,
      sub_eq_sub_iff_add_eq_add.mp hphi⟩
  · rintro ⟨hmem, hadd, hphi⟩
    exact ⟨⟨hmem 0, hmem 3, hmem 2, hmem 1⟩, sub_eq_sub_iff_add_eq_add.mpr hadd,
      sub_eq_sub_iff_add_eq_add.mpr hphi⟩

lemma prop61_g_product {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) (u : ZMod N) :
    prop61G B phi u (q 0) *
        star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
        prop61G B phi u (q 3) =
      if prop61QuadMem B q then
        exponential ((phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3)) * u)
      else 0 := by
  simp only [prop61G, indicator, star_mul]
  by_cases h0 : q 0 ∈ B <;> by_cases h1 : q 1 ∈ B <;>
    by_cases h2 : q 2 ∈ B <;> by_cases h3 : q 3 ∈ B
  all_goals simp only [h0, h1, h2, h3, if_true, if_false, one_mul, zero_mul, mul_zero,
    star_zero, star_one, prop61QuadMem, and_self, and_true]
  all_goals try {rfl}
  rw [star_exponential, star_exponential]
  calc
    _ = exponential (phi (q 0) * u +
        (-(phi (q 2) * u) + (-(phi (q 1) * u) + phi (q 3) * u))) := by
          rw [exponential_add, exponential_add, exponential_add]
          ring
    _ = _ := by
      congr 1
      ring

lemma prop61_sum_g_product {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) (q : Fin 4 → ZMod N) :
    (∑ u : ZMod N,
      prop61G B phi u (q 0) *
        star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
        prop61G B phi u (q 3)) =
      if prop61QuadMem B q ∧
          phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)
        then (N : Complex) else 0 := by
  simp_rw [prop61_g_product]
  by_cases hmem : prop61QuadMem B q
  · simp only [if_pos hmem, and_iff_right hmem, fejer_sum_exponential_mul]
    exact if_congr ⟨fun h => by linear_combination h, fun h => by linear_combination h⟩ rfl rfl
  · simp_rw [if_neg hmem, Finset.sum_const_zero]
    rw [if_neg (fun h => hmem h.1)]

lemma prop61_g_fourth_eq_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4) =
      (N : ℝ) ^ 2 * phiAdditiveCount B phi := by
  have h26 (u : ZMod N) := identity_2_6_holds N (prop61G B phi u)
  have hq (q : Fin 4 → ZMod N) : (if q 0 - q 1 = q 2 - q 3 then ∑ u : ZMod N,
      prop61G B phi u (q 0) * star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
        prop61G B phi u (q 3) else 0) =
      if prop61AltAdditive B phi q then (N : Complex) else 0 := by
    rw [prop61_sum_g_product]
    by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd, prop61AltAdditive]
  have hc : countWhere (prop61AltAdditive B phi) =
      (Finset.univ.filter (prop61AltAdditive B phi)).card :=
    congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
  rw [← prop61_alt_count_eq B phi, hc]
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  -- expand the fourth moments (2.6), sum the characters over `u`, and count
  simp_rw [h26, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_ite_irrel, Finset.sum_const_zero, hq, ← Finset.sum_filter, Finset.sum_const,
    nsmul_eq_mul]
  push_cast
  ring

end LeanProofs.GowersSzemeredi
