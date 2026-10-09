import GowersSzemeredi.Proofs16TrapezoidFourier
import GowersSzemeredi.Proofs16BohrAnnulus

/-! Quantitative L1 error for the discrete trapezoid approximation to a
Bohr indicator. The error includes the finite-size term 2 per frequency. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A [0,1]-valued sandwich differs from the middle indicator only in
its boundary band, by at most one at each point. -/
theorem indicator_sandwich_l1_le {N : Nat} [NeZero N]
    (I A O : Finset (ZMod N)) (hIA : I ⊆ A) (hAO : A ⊆ O)
    (g : ZMod N → Real) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hI : ∀ x ∈ I, g x = 1) (hO : ∀ x ∉ O, g x = 0) :
    (∑ x, ‖indicator A x - (g x : Complex)‖) ≤ (O \ I).card := by
  have hb (x : ZMod N) : ‖indicator A x - (g x : Complex)‖ ≤
      if x ∈ O \ I then (1 : Real) else 0 := by
    by_cases hband : x ∈ O \ I
    · rw [if_pos hband]
      by_cases hx : x ∈ A
      · have hnonneg : 0 ≤ 1 - g x := by linarith [(hg x).2]
        simp only [indicator, if_pos hx]
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hnonneg]
        linarith [(hg x).1]
      · simpa [indicator, hx, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hg x).1] using (hg x).2
    · rw [if_neg hband]
      by_cases hx : x ∈ O
      · have hi : x ∈ I := by simpa [Finset.mem_sdiff, hx] using hband
        simp [indicator, hIA hi, hI x hi]
      · have ha : x ∉ A := fun ha => hx (hAO ha)
        simp [indicator, ha, hO x hx]
  calc
    (∑ x, ‖indicator A x - (g x : Complex)‖) ≤
        ∑ x : ZMod N, if x ∈ O \ I then (1 : Real) else 0 :=
      Finset.sum_le_sum fun x _ => hb x
    _ = (O \ I).card := by
      rw [← Finset.sum_filter]
      simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
        nsmul_eq_mul, mul_one]

/-- The exact boundary-band estimate for a product of discrete trapezoids. -/
theorem trapezoid_product_l1_annulus {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (a c : Nat) (hca : c ≤ a) :
    (∑ x : ZMod N, ‖indicator (bohr K ((a : Real) / N)) x -
      ((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex)‖) ≤
      (bohr K (((a + c : Nat) : Real) / N) \
        bohr K (((a - c : Nat) : Real) / N)).card := by
  have hN : (0 : Real) ≤ N := Nat.cast_nonneg N
  apply indicator_sandwich_l1_le
  · exact bohr_mono_radius K (div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le a c) hN)
  · exact bohr_mono_radius K (div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_add_right a c) hN)
  · intro x
    exact (trapezoid_product_sandwich K a c x).2.2
  · intro x hx
    exact (trapezoid_product_sandwich K a c x).1 hx hca
  · intro x hx
    exact (trapezoid_product_sandwich K a c x).2.1 hx

/-- In prime modulus the L1 error is at most |K|(4c+2), including
both finite endpoints of each frequency band. -/
theorem trapezoid_product_l1_le {N : Nat} [NeZero N] [Fact N.Prime]
    (K : Finset (ZMod N)) (a c : Nat) (hca : c ≤ a) :
    (∑ x : ZMod N, ‖indicator (bohr K ((a : Real) / N)) x -
      ((∏ gamma ∈ K, trapezoid a c (gamma * x) : Real) : Complex)‖) ≤
      K.card * (4 * (c : Real) + 2) := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hsmall : 0 ≤ (a : Real) / N - (c : Real) / N := by
    rw [← sub_div]
    exact div_nonneg (sub_nonneg.mpr (by exact_mod_cast hca)) hN.le
  have h := bohr_annulus_card_le K (show 0 ≤ (c : Real) / N by positivity) hsmall
  have houter : ((a + c : Nat) : Real) / N = (a : Real) / N + (c : Real) / N := by
    push_cast; ring
  have hinner : ((a - c : Nat) : Real) / N = (a : Real) / N - (c : Real) / N := by
    rw [Nat.cast_sub hca, sub_div]
  have hscale : 4 * ((c : Real) / N) * N = 4 * (c : Real) := by field_simp
  have hband := trapezoid_product_l1_annulus K a c hca
  rw [houter, hinner] at hband
  rw [hscale] at h
  exact hband.trans h

end LeanProofs.GowersSzemeredi
