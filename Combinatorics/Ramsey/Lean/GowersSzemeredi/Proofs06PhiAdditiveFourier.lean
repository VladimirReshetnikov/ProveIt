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
  apply Finset.card_equiv
      ({ toFun q := ![q 0, q 3, q 2, q 1]
         invFun q := ![q 0, q 3, q 2, q 1]
         left_inv q := by
           funext i
           fin_cases i <;> rfl
         right_inv q := by
           funext i
           fin_cases i <;> rfl } : (Fin 4 → ((ZMod N))) ≃ (Fin 4 → ((ZMod N))))
  intro q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [prop61AltAdditive, prop61QuadMem, IsPhiAdditive, IsAdditiveQuadruple]
  constructor
  · rintro ⟨⟨h0, h1, h2, h3⟩, hadd, hphi⟩
    refine ⟨?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · rw [← sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hadd
    · rw [← sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hphi
  · rintro ⟨hmem, hadd, hphi⟩
    refine ⟨⟨hmem 0, hmem 3, hmem 2, hmem 1⟩, ?_, ?_⟩
    · rw [sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hadd
    · rw [sub_eq_sub_iff_add_eq_add]
      simpa [add_comm] using hphi

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
  · simp_rw [if_pos hmem]
    rw [fejer_sum_exponential_mul]
    by_cases hphi : phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)
    · have hcond : prop61QuadMem B q ∧
          phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3) := ⟨hmem, hphi⟩
      have hzero : phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) = 0 := by
        calc
          phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) =
              (phi (q 0) - phi (q 1)) - (phi (q 2) - phi (q 3)) := by abel
          _ = 0 := by rw [hphi, sub_self]
      rw [if_pos hzero, if_pos hcond]
    · have hne : phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) ≠ 0 := by
        intro hzero
        apply hphi
        apply sub_eq_zero.mp
        calc
          (phi (q 0) - phi (q 1)) - (phi (q 2) - phi (q 3)) =
              phi (q 0) - phi (q 1) - phi (q 2) + phi (q 3) := by abel
          _ = 0 := hzero
      have hcond : ¬(prop61QuadMem B q ∧
          phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3)) := fun h => hphi h.2
      rw [if_neg hne, if_neg hcond]
  · simp_rw [if_neg hmem]
    rw [if_neg (fun h => hmem h.1)]
    simp

lemma prop61_g_fourth_eq_count {N : Nat} [NeZero N]
    (B : Finset (ZMod N)) (phi : ZMod N → ZMod N) :
    (∑ u : ZMod N, ∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4) =
      (N : ℝ) ^ 2 * phiAdditiveCount B phi := by
  have hcomplex :
      (((∑ u : ZMod N, ∑ r : ZMod N,
          ‖fourier (prop61G B phi u) r‖ ^ 4 : ℝ)) : Complex) =
        (((N : ℝ) ^ 2 * countWhere (prop61AltAdditive B phi) : ℝ) : Complex) := by
    rw [Complex.ofReal_sum]
    calc
      (∑ u : ZMod N,
          ((∑ r : ZMod N, ‖fourier (prop61G B phi u) r‖ ^ 4 : ℝ) : Complex)) =
          ∑ u : ZMod N, (N : Complex) * ∑ q : Fin 4 → ZMod N,
            if q 0 - q 1 = q 2 - q 3 then
              prop61G B phi u (q 0) *
                star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
                prop61G B phi u (q 3)
            else 0 := by
              apply Finset.sum_congr rfl
              intro u _
              exact identity_2_6_holds N (prop61G B phi u)
      _ = (N : Complex) * (∑ q : Fin 4 → ZMod N,
          if q 0 - q 1 = q 2 - q 3 then
            ∑ u : ZMod N,
              prop61G B phi u (q 0) *
                star (prop61G B phi u (q 1) * prop61G B phi u (q 2)) *
                prop61G B phi u (q 3)
          else 0) := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro q _
            by_cases hadd : q 0 - q 1 = q 2 - q 3 <;> simp [hadd]
      _ = (N : Complex) * (∑ q : Fin 4 → ZMod N,
          if prop61AltAdditive B phi q then (N : Complex) else 0) := by
            congr 1
            apply Finset.sum_congr rfl
            intro q _
            rw [prop61_sum_g_product]
            by_cases hmem : prop61QuadMem B q <;>
              by_cases hadd : q 0 - q 1 = q 2 - q 3 <;>
              by_cases hphi : phi (q 0) - phi (q 1) = phi (q 2) - phi (q 3) <;>
              simp [prop61AltAdditive, hmem, hadd, hphi]
      _ = (((N : ℝ) ^ 2 * countWhere (prop61AltAdditive B phi) : ℝ) : Complex) := by
            push_cast
            unfold countWhere
            rw [← Finset.sum_filter]
            simp only [Finset.sum_const, nsmul_eq_mul]
            ring_nf
            congr 1
            norm_cast
            apply congrArg Finset.card
            ext q
            simp
  rw [prop61_alt_count_eq B phi] at hcomplex
  exact Complex.ofReal_injective hcomplex

end LeanProofs.GowersSzemeredi
