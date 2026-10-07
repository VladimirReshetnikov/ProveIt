-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.GroupTheory.Index
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest
import OAI.Combinatorics.Progressions.Fourier.FiniteSpectrumCutoff
import OAI.Compat.Core

namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {H : Type*} [AddCommGroup H] [Fintype H]

noncomputable def finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) : ℂ :=
  𝔼 x, f x * star (χ x)

theorem addChar_sub_star (χ : AddChar H ℂ) (x y : H) :
    χ (x - y) = χ x * star (χ y) := by
  rw [AddChar.map_sub_eq_div, div_eq_mul_inv, AddChar.inv_apply_eq_conj]
  rfl

theorem star_finiteFourierCoeff (f : H → ℂ) (χ : AddChar H ℂ) :
    star (finiteFourierCoeff f χ) = 𝔼 x, star (f x) * χ x := by
  rw [finiteFourierCoeff, ← expect_star]
  apply Finset.expect_congr rfl
  intro x _
  simp only [star_mul, star_star]
  ring

theorem finiteFourier_inversion (f : H → ℂ) (x : H) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) = f x := by
  classical
  calc
    _ = 𝔼 y, f y * (∑ χ : AddChar H ℂ, χ (x - y)) := by
      simp only [finiteFourierCoeff, Finset.expect_mul]
      rw [← Finset.expect_sum_comm]
      apply Finset.expect_congr rfl
      intro y _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = 𝔼 y, if x = y then (Fintype.card H : ℂ) * f x else 0 := by
      apply Finset.expect_congr rfl
      intro y _
      rw [AddChar.sum_apply_eq_ite]
      by_cases hxy : x = y
      · subst y
        simp [mul_comm]
      · simp [sub_eq_zero, hxy]
    _ = _ := by
      have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
      rw [Fintype.expect_eq_sum_div_card, Finset.sum_eq_single x]
      · simp [hc]
      · intro y _ hy
        simp only [ite_eq_right (Ne.symm hy)]
      · simp

theorem finiteFourier_inner (f g : H → ℂ) :
    (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * star (finiteFourierCoeff g χ)) =
      𝔼 x, f x * star (g x) := by
  simp_rw [star_finiteFourierCoeff, Finset.mul_expect]
  rw [← Finset.expect_sum_comm]
  apply Finset.expect_congr rfl
  intro x _
  calc
    _ = (∑ χ : AddChar H ℂ, finiteFourierCoeff f χ * χ x) * star (g x) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    _ = _ := by rw [finiteFourier_inversion]

theorem finiteFourier_parseval (f : H → ℂ) :
    (∑ χ : AddChar H ℂ, ‖finiteFourierCoeff f χ‖ ^ 2) = 𝔼 x, ‖f x‖ ^ 2 := by
  have h := congrArg Complex.re (finiteFourier_inner f f)
  simpa only [Complex.re_sum, expect_re, mul_star_re_eq_norm_sq] using h

end Erdos3

end

section

open Finset
open scoped BigOperators

namespace Erdos3

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def fourierL1 (f : G → ℂ) : ℝ :=
  ∑ ψ : AddChar G ℂ, ‖finiteFourierCoeff f ψ‖

theorem norm_sub_translate_le_fourier_sum (f : G → ℂ) (t x : G) :
    ‖f (x - t) - f x‖ ≤
      ∑ ψ : AddChar G ℂ,
        ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
  classical
  rw [← finiteFourier_inversion f (x - t),
    ← finiteFourier_inversion f x, ← Finset.sum_sub_distrib]
  calc
    ‖∑ ψ : AddChar G ℂ,
        (finiteFourierCoeff f ψ * ψ (x - t) -
          finiteFourierCoeff f ψ * ψ x)‖
        ≤ ∑ ψ : AddChar G ℂ,
            ‖finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x‖ :=
          norm_sum_le _ _
    _ = ∑ ψ : AddChar G ℂ,
          ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ := by
      apply sum_congr rfl
      intro ψ _
      have hfactor :
          finiteFourierCoeff f ψ * ψ (x - t) -
              finiteFourierCoeff f ψ * ψ x =
            (finiteFourierCoeff f ψ * ψ x) * (ψ (-t) - 1) := by
        have hmap : ψ (x - t) = ψ x * ψ (-t) := by
          rw [sub_eq_add_neg, ψ.map_add_eq_mul]
        rw [hmap]
        ring
      rw [hfactor, norm_mul, norm_mul, AddChar.norm_apply, mul_one]

theorem norm_sub_translate_le_mul_fourierL1
    (f : G → ℂ) (t x : G) {delta : ℝ} (_hdelta : 0 ≤ delta)
    (hann : ∀ ψ : AddChar G ℂ, ‖ψ (-t) - 1‖ ≤ delta) :
    ‖f (x - t) - f x‖ ≤ delta * fourierL1 f := by
  classical
  calc
    ‖f (x - t) - f x‖ ≤
        ∑ ψ : AddChar G ℂ,
          ‖finiteFourierCoeff f ψ‖ * ‖ψ (-t) - 1‖ :=
      norm_sub_translate_le_fourier_sum f t x
    _ ≤ ∑ ψ : AddChar G ℂ,
        ‖finiteFourierCoeff f ψ‖ * delta := by
      gcongr with ψ
      exact hann ψ
    _ = delta * fourierL1 f := by
      rw [fourierL1]
      calc
        Finset.univ.sum
            (fun ψ : AddChar G ℂ ↦ ‖finiteFourierCoeff f ψ‖ * delta) =
            Finset.univ.sum
              (fun ψ : AddChar G ℂ ↦ ‖finiteFourierCoeff f ψ‖) * delta :=
          (Finset.sum_mul _ _ _).symm
        _ = _ := mul_comm _ _

theorem norm_sub_translate_le_spectrum_cutoff
    (f : G → ℂ) (Omega : Finset (AddChar G ℂ)) (t x : G)
    {theta : ℝ} (_htheta : 0 ≤ theta)
    (hann : ∀ psi ∈ Omega, ‖psi (-t) - 1‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤
      theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
        ‖finiteFourierCoeff f psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖finiteFourierCoeff f psi‖ := by
  classical
  calc
    ‖f (x - t) - f x‖ ≤
        ∑ psi : AddChar G ℂ,
          ‖finiteFourierCoeff f psi‖ * ‖psi (-t) - 1‖ :=
      norm_sub_translate_le_fourier_sum f t x
    _ = ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖finiteFourierCoeff f psi‖ * ‖psi (-t) - 1‖ +
        ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖finiteFourierCoeff f psi‖ * ‖psi (-t) - 1‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
        (p := fun psi : AddChar G ℂ ↦ psi ∈ Omega)]
    _ ≤ ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖finiteFourierCoeff f psi‖ * theta +
        ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖finiteFourierCoeff f psi‖ * 2 := by
      gcongr with psi hpsi psi hpsi
      · exact hann psi (by simpa using hpsi)
      · calc
          ‖psi (-t) - 1‖ ≤ ‖psi (-t)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
          _ = 2 := by norm_num
    _ = theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖finiteFourierCoeff f psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖finiteFourierCoeff f psi‖ := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      ring

theorem norm_sub_translate_le_of_uniform_approx_and_spectrum_cutoff
    (f p : G → ℂ) (Omega : Finset (AddChar G ℂ)) (t x : G)
    {delta theta : ℝ} (_hdelta : 0 ≤ delta) (htheta : 0 ≤ theta)
    (happrox : ∀ y, ‖p y - f y‖ ≤ delta)
    (hann : ∀ psi ∈ Omega, ‖psi (-t) - 1‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤
      2 * delta +
        theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖finiteFourierCoeff p psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖finiteFourierCoeff p psi‖ := by
  classical
  have hdecomp : f (x - t) - f x =
      (f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x) := by ring
  rw [hdecomp]
  calc
    ‖(f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x)‖ ≤
        ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ + ‖p x - f x‖ := by
      calc
        _ ≤ ‖(f (x - t) - p (x - t)) + (p (x - t) - p x)‖ +
            ‖p x - f x‖ := norm_add_le _ _
        _ ≤ ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ +
            ‖p x - f x‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ delta + ‖p (x - t) - p x‖ + delta := by
      gcongr
      · simpa only [norm_sub_rev] using happrox (x - t)
      · exact happrox x
    _ ≤ delta +
        (theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
            ‖finiteFourierCoeff p psi‖ +
          2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
            ‖finiteFourierCoeff p psi‖) + delta := by
      gcongr
      exact norm_sub_translate_le_spectrum_cutoff p Omega t x htheta hann
    _ = 2 * delta +
        theta * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∈ Omega),
          ‖finiteFourierCoeff p psi‖ +
        2 * ∑ psi ∈ Finset.univ.filter (fun psi ↦ psi ∉ Omega),
          ‖finiteFourierCoeff p psi‖ := by ring

omit [Fintype G] in

lemma norm_character_neg_sub_one [Finite G] (psi : AddChar G ℂ) (t : G) :
    ‖psi (-t) - 1‖ = ‖1 - psi t‖ := by
  rw [psi.map_neg_eq_inv]
  have hne : psi t ≠ 0 := by
    intro h
    have := AddChar.norm_apply psi t
    simp [h] at this
  calc
    ‖(psi t)⁻¹ - 1‖ = ‖(psi t)⁻¹ * (1 - psi t)‖ := by
      congr 1
      field_simp
    _ = ‖1 - psi t‖ := by
      rw [norm_mul, norm_inv, AddChar.norm_apply, inv_one, one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteImageMass {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) : ℝ :=
  p.mean (fun x => if Y x = z then 1 else 0)

noncomputable def finiteImageCharacteristic {X H : Type*} [Fintype X] [AddCommGroup H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (χ : AddChar H ℂ) : ℂ :=
  p.complexMean (fun x => χ (Y x))

theorem finiteImageCharacteristic_norm_le_one {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] (p : FiniteProbabilityWeights X) (Y : X → H) (χ : AddChar H ℂ) :
    ‖finiteImageCharacteristic p Y χ‖ ≤ 1 := by
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [AddChar.norm_apply, p.mean_const])

theorem finiteImageFourier_inversion {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    (∑ χ : AddChar H ℂ, finiteImageCharacteristic p Y χ * star (χ z)) =
      (Fintype.card H : ℂ) * finiteImageMass p Y z := by
  classical
  calc
    _ = ∑ x, (p.weight x : ℂ) * (∑ χ : AddChar H ℂ, χ (Y x - z)) := by
      simp only [finiteImageCharacteristic, FiniteProbabilityWeights.complexMean, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ _
      rw [addChar_sub_star]
      ring
    _ = (Fintype.card H : ℂ) * finiteImageMass p Y z := by
      simp only [AddChar.sum_apply_eq_ite, sub_eq_zero, finiteImageMass,
        FiniteProbabilityWeights.mean, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : Y x = z <;> simp [hx, mul_comm]

theorem finiteImageFourier_truncation {X H : Type*} [Fintype X]
    [AddCommGroup H] [Fintype H] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (S : Finset (AddChar H ℂ)) (z : H)
    {scale : ℝ} (hscale : 0 ≤ scale) :
    ‖(scale : ℂ) * finiteImageMass p Y z -
      ((scale : ℂ) / Fintype.card H) * ∑ χ ∈ S, finiteImageCharacteristic p Y χ * star (χ z)‖ ≤
      (scale / Fintype.card H) * spectrumTail S (fun χ => ‖finiteImageCharacteristic p Y χ‖) := by
  have hc : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he : (scale : ℂ) * finiteImageMass p Y z = ((scale : ℂ) / Fintype.card H) *
      ∑ χ : AddChar H ℂ, finiteImageCharacteristic p Y χ * star (χ z) := by
    rw [finiteImageFourier_inversion]
    field_simp
  rw [he, ← mul_sub, norm_mul]
  have hn : ‖(scale : ℂ) / Fintype.card H‖ = scale / Fintype.card H := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hscale, Complex.norm_natCast]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_series_truncation_le S _ (fun χ => star (χ z))
    (fun χ => by simp only [norm_star, AddChar.norm_apply, le_refl])

end Erdos3

end

section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.Chang

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def spectrumSum (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  ∑ x ∈ A, psi x

noncomputable def largeSpectrum (A : Finset G) (eta : ℝ) : Finset (AddChar G ℂ) :=
  Finset.univ.filter fun psi ↦ eta * A.card ≤ ‖spectrumSum A psi‖

@[simp]
theorem mem_largeSpectrum {A : Finset G} {eta : ℝ} {psi : AddChar G ℂ} :
    psi ∈ largeSpectrum A eta ↔ eta * A.card ≤ ‖spectrumSum A psi‖ := by
  simp [largeSpectrum]

end Erdos3.Chang

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

noncomputable def additiveCharacterKernel (χ : AddChar G ℂ) : AddSubgroup G where
  carrier := {x | χ x = 1}
  zero_mem' := χ.map_zero_eq_one
  add_mem' := by
    intro x y hx hy
    change χ (x + y) = 1
    rw [AddChar.map_add_eq_mul, hx, hy, one_mul]
  neg_mem' := by
    intro x hx
    change χ (-x) = 1
    rw [AddChar.map_neg_eq_inv, hx, inv_one]

theorem additiveCharacterKernel_ne_top {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    additiveCharacterKernel χ ≠ ⊤ := by
  intro h
  apply hχ
  ext x
  change χ x = 1
  have hx : x ∈ additiveCharacterKernel χ := by rw [h]; trivial
  exact hx

variable [Fintype G]

theorem primePowerCharacter_kernel_index {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    p ≤ (additiveCharacterKernel χ).index := by
  have hd : (additiveCharacterKernel χ).index ∣ p ^ a := by
    rw [← hG, ← Nat.card_eq_fintype_card]
    exact (additiveCharacterKernel χ).index_dvd_card
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow hp).mp hd
  have hbpos : 0 < b := by
    by_contra hn
    have hbzero : b = 0 := by omega
    rw [hbzero, pow_zero] at hb
    exact additiveCharacterKernel_ne_top hχ ((additiveCharacterKernel χ).index_eq_one.mp hb)
  rw [hb]
  simpa only [pow_one] using Nat.pow_le_pow_right hp.one_le hbpos

theorem primePowerCharacter_kernel_probability {p a : ℕ} (hp : p.Prime)
    (hG : Fintype.card G = p ^ a) {χ : AddChar G ℂ} (hχ : χ ≠ 0) :
    (𝔼 x : G, if χ x = 1 then (1 : ℝ) else 0) ≤ (p : ℝ)⁻¹ := by
  classical
  let K := additiveCharacterKernel χ
  have hindex := primePowerCharacter_kernel_index hp hG hχ
  have hc : (Fintype.card K : ℝ) * K.index = Fintype.card G := by
    have h : Fintype.card K * K.index = Fintype.card G := by
      simpa only [Nat.card_eq_fintype_card] using K.card_mul_index
    exact_mod_cast h
  have hN : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hcard : (Finset.univ.filter (fun x : G => χ x = 1)).card = Fintype.card K := by
    simp [K, additiveCharacterKernel, Fintype.card_subtype]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [Finset.sum_boole, hcard]
  apply (div_le_iff₀ hN).mpr
  have hi : (p : ℝ) ≤ K.index := by exact_mod_cast hindex
  calc
    _ ≤ (p : ℝ)⁻¹ * ((Fintype.card K : ℝ) * K.index) := by
      apply (le_inv_mul_iff₀ hp0).mpr
      nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card K)]
    _ = _ := by rw [hc]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def finiteSetAverage (A : Finset G) (f : G → ℂ) (x : G) : ℂ :=
  𝔼 a ∈ A, f (x - a)

noncomputable def setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) : ℂ :=
  𝔼 a ∈ A, star (psi a)

theorem finiteFourierCoeff_translate (f : G → ℂ) (a : G) (psi : AddChar G ℂ) :
    finiteFourierCoeff (fun x => f (x - a)) psi = star (psi a) * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff
  calc
    (𝔼 x, f (x - a) * star (psi x)) = 𝔼 x, f x * star (psi (x + a)) := by
      apply Fintype.expect_equiv (Equiv.subRight a)
      intro x
      simp
    _ = star (psi a) * 𝔼 x, f x * star (psi x) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      rw [AddChar.map_add_eq_mul, star_mul]
      ring

theorem finiteFourierCoeff_finiteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) :
    finiteFourierCoeff (finiteSetAverage A f) psi =
      setFourierMultiplier A psi * finiteFourierCoeff f psi := by
  unfold finiteFourierCoeff finiteSetAverage
  simp_rw [Finset.expect_mul]
  rw [Finset.expect_comm]
  change (𝔼 a ∈ A, finiteFourierCoeff (fun x => f (x - a)) psi) = _
  simp_rw [finiteFourierCoeff_translate]
  rw [← Finset.expect_mul]
  rfl

omit [Fintype G] in
theorem setFourierMultiplier_eq (A : Finset G) (psi : AddChar G ℂ) :
    setFourierMultiplier A psi = star (Chang.spectrumSum A psi) / (A.card : ℂ) := by
  simp only [setFourierMultiplier, Finset.expect_eq_sum_div_card, Chang.spectrumSum, star_sum]

omit [Fintype G] in
theorem norm_setFourierMultiplier (A : Finset G) (psi : AddChar G ℂ) :
    ‖setFourierMultiplier A psi‖ = ‖Chang.spectrumSum A psi‖ / A.card := by
  rw [setFourierMultiplier_eq, norm_div, norm_star, Complex.norm_natCast]

theorem norm_setFourierMultiplier_le_one {A : Finset G} (hA : A.Nonempty)
    (psi : AddChar G ℂ) : ‖setFourierMultiplier A psi‖ ≤ 1 := by
  apply (RCLike.norm_expect_le (K := ℂ)).trans
  simp only [norm_star, AddChar.norm_apply, Finset.expect_const hA]
  exact le_rfl

theorem mem_largeSpectrum_iff_le_multiplier {A : Finset G} (hA : A.Nonempty)
    (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ Chang.largeSpectrum A eta ↔ eta ≤ ‖setFourierMultiplier A psi‖ := by
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  rw [Chang.mem_largeSpectrum, norm_setFourierMultiplier, le_div_iff₀ hcard]

noncomputable def iteratedFiniteSetAverage (A : Finset G) (f : G → ℂ) : ℕ → G → ℂ
  | 0 => f
  | n + 1 => finiteSetAverage A (iteratedFiniteSetAverage A f n)

theorem finiteFourierCoeff_iteratedFiniteSetAverage
    (A : Finset G) (f : G → ℂ) (psi : AddChar G ℂ) (n : ℕ) :
    finiteFourierCoeff (iteratedFiniteSetAverage A f n) psi =
      setFourierMultiplier A psi ^ n * finiteFourierCoeff f psi := by
  induction n with
  | zero => simp [iteratedFiniteSetAverage]
  | succ n ih =>
      rw [iteratedFiniteSetAverage, finiteFourierCoeff_finiteSetAverage, ih, pow_succ]
      ring

end Erdos3

end

section

noncomputable section

open Finset Function Real
open scoped BigOperators ComplexConjugate NNReal

namespace Erdos3.RelativeChangSanders

variable {G : Type*} [Fintype G] [AddCommGroup G]

def IsWeightedDissociated (mu : G → ℝ) (K : ℝ)
    (Delta : Finset (AddChar G ℂ)) : Prop :=
  ∀ u : AddChar G ℂ → ℂ,
    (∀ psi ∈ Delta, ‖u psi‖ ≤ 1) →
      ∑ x : G, mu x *
        ∏ psi ∈ Delta, (1 + (u psi * psi x).re) ≤ exp K

def weightedSpectrumSum (f : G → ℝ) (psi : AddChar G ℂ) : ℂ :=
  ∑ x : G, (f x : ℂ) * psi x

def relativeLargeSpectrum (mu f : G → ℝ) (eta : ℝ) :
    Finset (AddChar G ℂ) :=
    Finset.univ.filter fun psi ↦
    eta * (∑ x : G, f x * mu x) ≤
      ‖∑ x : G, (f x * mu x : ℝ) * psi x‖

@[simp] theorem mem_relativeLargeSpectrum {mu f : G → ℝ} {eta : ℝ}
    {psi : AddChar G ℂ} :
    psi ∈ relativeLargeSpectrum mu f eta ↔
      eta * (∑ x : G, f x * mu x) ≤
        ‖∑ x : G, (f x * mu x : ℝ) * psi x‖ := by
  simp [relativeLargeSpectrum]

end Erdos3.RelativeChangSanders

end

end

section

namespace Erdos3.Chang

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
theorem spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi =
      spectrumSum T psi * psi (-z) := by
  unfold spectrumSum
  rw [Finset.sum_map]
  simp only [Equiv.toEmbedding_apply, Equiv.subRight_apply,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  rw [Finset.sum_mul]

theorem norm_spectrumSum_map_subRight (T : Finset G) (z : G) (psi : AddChar G ℂ) :
    ‖spectrumSum (T.map (Equiv.subRight z).toEmbedding) psi‖ = ‖spectrumSum T psi‖ := by
  rw [spectrumSum_map_subRight, norm_mul, AddChar.norm_apply, mul_one]

theorem mem_largeSpectrum_map_subRight_iff
    (T : Finset G) (z : G) (eta : ℝ) (psi : AddChar G ℂ) :
    psi ∈ largeSpectrum (T.map (Equiv.subRight z).toEmbedding) eta ↔
      psi ∈ largeSpectrum T eta := by
  rw [mem_largeSpectrum, mem_largeSpectrum, Finset.card_map, norm_spectrumSum_map_subRight]

end Erdos3.Chang

end

section

open scoped BigOperators

namespace Erdos3

variable {G : Type*} [AddCommGroup G] [Fintype G]

theorem iteratedFiniteSetAverage_translate_le
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖iteratedFiniteSetAverage X f m (x - t) - iteratedFiniteSetAverage X f m x‖ ≤
      (theta + 2 * eta ^ m) * fourierL1 f := by
  apply (norm_sub_translate_le_fourier_sum (iteratedFiniteSetAverage X f m) t x).trans
  calc
    (∑ psi : AddChar G ℂ,
        ‖finiteFourierCoeff (iteratedFiniteSetAverage X f m) psi‖ * ‖psi (-t) - 1‖) ≤
        ∑ psi : AddChar G ℂ, (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
      apply Finset.sum_le_sum
      intro psi _
      rw [finiteFourierCoeff_iteratedFiniteSetAverage, norm_mul, norm_pow,
        norm_character_neg_sub_one]
      have hmu := norm_setFourierMultiplier_le_one hX psi
      by_cases hlarge : eta ≤ ‖setFourierMultiplier X psi‖
      · have hpow : ‖setFourierMultiplier X psi‖ ^ m ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) hmu
        have hp := hphase psi ((mem_largeSpectrum_iff_le_multiplier hX eta psi).2 hlarge)
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              1 * ‖finiteFourierCoeff f psi‖ * theta := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hepow : 0 ≤ eta ^ m := pow_nonneg heta m
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
      · have htail : ‖setFourierMultiplier X psi‖ ^ m ≤ eta ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (le_of_not_ge hlarge) m
        have hchord : ‖1 - psi t‖ ≤ 2 := by
          calc
            ‖1 - psi t‖ ≤ ‖(1 : ℂ)‖ + ‖psi t‖ := norm_sub_le _ _
            _ = 2 := by norm_num
        calc
          ‖setFourierMultiplier X psi‖ ^ m * ‖finiteFourierCoeff f psi‖ * ‖1 - psi t‖ ≤
              eta ^ m * ‖finiteFourierCoeff f psi‖ * 2 := by gcongr
          _ ≤ (theta + 2 * eta ^ m) * ‖finiteFourierCoeff f psi‖ := by
            have hf : 0 ≤ ‖finiteFourierCoeff f psi‖ := norm_nonneg _
            nlinarith
    _ = (theta + 2 * eta ^ m) * fourierL1 f := by rw [fourierL1, Finset.mul_sum]

theorem translate_le_of_iteratedFiniteSetAverage_approx
    {X : Finset G} (hX : X.Nonempty) (m : ℕ) (f : G → ℂ)
    {delta eta theta : ℝ} (heta : 0 ≤ eta) (htheta : 0 ≤ theta) (t x : G)
    (happrox : ∀ y, ‖iteratedFiniteSetAverage X f m y - f y‖ ≤ delta)
    (hphase : ∀ psi ∈ Chang.largeSpectrum X eta, ‖1 - psi t‖ ≤ theta) :
    ‖f (x - t) - f x‖ ≤ 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by
  let p := iteratedFiniteSetAverage X f m
  have hdecomp : f (x - t) - f x =
      (f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x) := by ring
  rw [hdecomp]
  calc
    ‖(f (x - t) - p (x - t)) + (p (x - t) - p x) + (p x - f x)‖ ≤
        ‖f (x - t) - p (x - t)‖ + ‖p (x - t) - p x‖ + ‖p x - f x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ delta + ((theta + 2 * eta ^ m) * fourierL1 f) + delta := by
      apply add_le_add
      · apply add_le_add
        · simpa only [norm_sub_rev] using happrox (x - t)
        · exact iteratedFiniteSetAverage_translate_le hX m f heta htheta t x hphase
      · exact happrox x
    _ = 2 * delta + (theta + 2 * eta ^ m) * fourierL1 f := by ring

end Erdos3

end

end OAI
