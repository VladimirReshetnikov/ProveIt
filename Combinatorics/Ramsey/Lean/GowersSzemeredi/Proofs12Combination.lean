import GowersSzemeredi.Proofs12Restriction

/-!
# Combining the Section 12 estimates

This file proves Lemma 12.6 from Lemma 12.4 and the density-uniform form of
Lemma 12.5.  The latter is essential: the density of `B` need only be bounded
below, so the sufficiently-large threshold cannot depend on its exact value.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma lemma126_constant :
    (2 : Real) ^ (-((2 : Real) ^ 37)) =
      ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) := by
  rw [Real.rpow_neg (by positivity)]
  rw [show (2 : Real) ^ 37 = 2 * (((2 : Nat) ^ 36 : Nat) : Real) by norm_num]
  rw [Real.rpow_mul_natCast (by norm_num : (0 : Real) ≤ 2)]
  norm_num only [Real.rpow_two]
  rw [← inv_pow]
  norm_num

private lemma lemma126_target (beta gamma eta : Real) :
    ((beta ^ 112 * gamma ^ 336) * eta / 4) ^ ((2 : Nat) ^ 36) =
      ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) *
        beta ^ (112 * ((2 : Nat) ^ 36)) *
        gamma ^ (336 * ((2 : Nat) ^ 36)) *
        eta ^ ((2 : Nat) ^ 36) := by
  simp only [div_eq_mul_inv, mul_pow, pow_mul, inv_pow]
  ring

private lemma lemma126_coefficient (beta gamma eta : Real)
    (hbeta : 0 < beta) (hbeta_one : beta ≤ 1)
    (hgamma : 0 < gamma) (hgamma_one : gamma ≤ 1) (heta : 0 < eta) :
    (2 : Real) ^ (-((2 : Real) ^ 37)) * beta ^ ((2 : Nat) ^ 43) *
          gamma ^ ((2 : Nat) ^ 45) * eta ^ ((2 : Nat) ^ 36) ≤
      ((beta ^ 112 * gamma ^ 336) * eta / 4) ^ ((2 : Nat) ^ 36) := by
  have hbetaExponent : 112 * ((2 : Nat) ^ 36) ≤ (2 : Nat) ^ 43 := by
    norm_num
  have hgammaExponent : 336 * ((2 : Nat) ^ 36) ≤ (2 : Nat) ^ 45 := by
    norm_num
  have hbetaPow : beta ^ ((2 : Nat) ^ 43) ≤
      beta ^ (112 * ((2 : Nat) ^ 36)) :=
    pow_le_pow_of_le_one hbeta.le hbeta_one hbetaExponent
  have hgammaPow : gamma ^ ((2 : Nat) ^ 45) ≤
      gamma ^ (336 * ((2 : Nat) ^ 36)) :=
    pow_le_pow_of_le_one hgamma.le hgamma_one hgammaExponent
  rw [lemma126_constant, lemma126_target]
  have hc0 : 0 ≤ ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) := by positivity
  have hgammaHigh0 : 0 ≤ gamma ^ ((2 : Nat) ^ 45) :=
    pow_nonneg hgamma.le _
  have heta0 : 0 ≤ eta ^ ((2 : Nat) ^ 36) := pow_nonneg heta.le _
  calc
    ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) * beta ^ ((2 : Nat) ^ 43) *
          gamma ^ ((2 : Nat) ^ 45) * eta ^ ((2 : Nat) ^ 36) ≤
        ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) *
          beta ^ (112 * ((2 : Nat) ^ 36)) *
          gamma ^ ((2 : Nat) ^ 45) * eta ^ ((2 : Nat) ^ 36) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbetaPow hc0) hgammaHigh0) heta0
    _ ≤ ((4 : Real)⁻¹) ^ ((2 : Nat) ^ 36) *
          beta ^ (112 * ((2 : Nat) ^ 36)) *
          gamma ^ (336 * ((2 : Nat) ^ 36)) * eta ^ ((2 : Nat) ^ 36) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgammaPow
          (mul_nonneg hc0 (pow_nonneg hbeta.le _))) heta0

private lemma lemma126_fourier_norm_le {N : Nat} [NeZero N]
    (g : ZMod N → Complex) (hg : DiscValued g) (r : ZMod N) :
    ‖fourier g r‖ ≤ (N : Real) := by
  calc
    ‖fourier g r‖ ≤
        ∑ x : ZMod N, ‖exponential (-(x * r)) * g x‖ := by
      simpa only [fourier, ZMod.dft_apply, smul_eq_mul, exponential] using
        norm_sum_le (Finset.univ : Finset (ZMod N))
          (fun x : ZMod N ↦ exponential (-(x * r)) * g x)
    _ ≤ ∑ _x : ZMod N, (1 : Real) := by
      apply Finset.sum_le_sum
      intro x _
      rw [norm_mul]
      have hexponential : ‖exponential (-(x * r))‖ = 1 :=
        (ZMod.stdAddChar (N := N)).norm_apply (-(x * r))
      rw [hexponential, one_mul]
      exact hg x
    _ = (N : Real) := by simp

private lemma lemma126_gamma_le_one {N : Nat} [NeZero N]
    (beta gamma : Real) (f : ZMod N → Complex) (B : Finset (Pair N))
    (phi : Pair N → ZMod N) (hbeta : 0 < beta) (hf : DiscValued f)
    (hcard : beta * (N : Real) ^ 2 ≤ B.card)
    (hlarge : ∀ z, z ∈ B →
      gamma * N ≤ ‖secondDifferenceFourier f z.1 z.2 (phi z)‖) :
    gamma ≤ 1 := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hBposReal : 0 < (B.card : Real) :=
    (mul_pos hbeta (pow_pos hN _)).trans_le hcard
  have hBpos : 0 < B.card := by exact_mod_cast hBposReal
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hBpos
  have hlower := hlarge z hz
  have hdisc : DiscValued (secondDifference f z.1 z.2) :=
    difference_discValued (difference_discValued hf z.1) z.2
  have hupper :
      ‖secondDifferenceFourier f z.1 z.2 (phi z)‖ ≤ (N : Real) := by
    exact lemma126_fourier_norm_le (secondDifference f z.1 z.2) hdisc (phi z)
  nlinarith

private lemma lemma126_beta_le_one {N : Nat} [NeZero N]
    (beta : Real) (B : Finset (Pair N))
    (hcard : beta * (N : Real) ^ 2 ≤ B.card) : beta ≤ 1 := by
  have hN : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hcardNat : B.card ≤ N ^ 2 := by
    calc
      B.card ≤ (Finset.univ : Finset (Pair N)).card :=
        Finset.card_le_card (Finset.subset_univ B)
      _ = Fintype.card (Pair N) := Finset.card_univ
      _ = N ^ 2 := by simp [Pair, pow_two]
  have hcardReal : (B.card : Real) ≤ (N : Real) ^ 2 := by
    exact_mod_cast hcardNat
  nlinarith [pow_pos hN 2]

/-- **Lemma 12.6.** The Fourier hypothesis produces a large restriction on
which `phi` respects at least a `1 - eta` proportion of all arrangements. -/
theorem lemma_12_6_holds : lemma_12_6 := by
  intro beta gamma eta hbeta hgamma heta heta_one
  let alpha : Real := beta ^ 112 * gamma ^ 336
  have halpha : 0 < alpha := by
    dsimp [alpha]
    positivity
  obtain ⟨N0, hN0⟩ :=
    lemma_12_5_uniform_holds alpha eta halpha heta heta_one
  refine ⟨N0, ?_⟩
  intro N _ hN f B phi hf hBcard hlarge
  have hNreal : 0 < (N : Real) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hNsquare : 0 < (N : Real) ^ 2 := pow_pos hNreal _
  let delta : Real := (B.card : Real) / (N : Real) ^ 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact div_pos ((mul_pos hbeta hNsquare).trans_le hBcard) hNsquare
  have hbetaDelta : beta ≤ delta := by
    dsimp [delta]
    exact (le_div_iff₀ hNsquare).2 hBcard
  have hcardExact : (B.card : Real) = delta * (N : Real) ^ 2 := by
    dsimp [delta]
    exact (div_mul_cancel₀ (B.card : Real) hNsquare.ne').symm
  have hmany := lemma_12_4_holds N delta gamma f B phi hdelta hgamma hf
    hcardExact hlarge
  have hbetaPow : beta ^ 112 ≤ delta ^ 112 :=
    pow_le_pow_left₀ hbeta.le hbetaDelta _
  have hmanyUniform : alpha * (N : Real) ^ 32 ≤
      (respectedArrangementCount 8 B phi : Real) := by
    dsimp [alpha]
    calc
      beta ^ 112 * gamma ^ 336 * (N : Real) ^ 32 ≤
          delta ^ 112 * gamma ^ 336 * (N : Real) ^ 32 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hbetaPow (pow_nonneg hgamma.le _))
          (pow_nonneg hNreal.le _)
      _ ≤ (respectedArrangementCount 8 B phi : Real) := hmany
  obtain ⟨B', hB'B, harrangements, hrespected⟩ :=
    hN0 N hN B phi hmanyUniform
  have hbetaOne := lemma126_beta_le_one beta B hBcard
  have hgammaOne := lemma126_gamma_le_one beta gamma f B phi hbeta hf hBcard hlarge
  have hcoefficient :=
    lemma126_coefficient beta gamma eta hbeta hbetaOne hgamma hgammaOne heta
  refine ⟨B', hB'B, ?_, hrespected⟩
  exact (mul_le_mul_of_nonneg_right hcoefficient
    (pow_nonneg hNreal.le 32)).trans harrangements

end LeanProofs.GowersSzemeredi
