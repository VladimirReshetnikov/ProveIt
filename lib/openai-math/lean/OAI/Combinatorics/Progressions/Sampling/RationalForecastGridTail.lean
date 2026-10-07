import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.Fourier.FiniteCharacterOrderTail
import OAI.Combinatorics.Progressions.Probability.IntervalDivisorProbability
import OAI.Combinatorics.Progressions.Sampling.TranslatedPartialPeriodicGridIntegrability

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def rationalOutputDensity {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : ℝ :=
  Fintype.card (J → ZMod N) * finiteImageMass p (fun x j => (Y x j : ZMod N)) b

theorem rationalOutputDensity_nonneg {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) : 0 ≤ rationalOutputDensity p Y N b := by
  unfold rationalOutputDensity finiteImageMass
  exact mul_nonneg (Nat.cast_nonneg _) (p.mean_nonneg (fun _ => by split_ifs <;> norm_num))

theorem rationalOutputDensity_test {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (test : (J → ZMod N) → ℂ) :
    (𝔼 b, (rationalOutputDensity p Y N b : ℂ) * test b) =
      p.complexMean (fun x => test (fun j => (Y x j : ZMod N))) := by
  let F := fun x j => (Y x j : ZMod N)
  have hmass (b) : finiteImageMass p F b = (p.fiberLaw F).weight b := by
    unfold finiteImageMass FiniteProbabilityWeights.fiberLaw FiniteProbabilityWeights.fiberMean
    congr 1
    funext x
    split_ifs <;> rfl
  have hcard : (Fintype.card (J → ZMod N) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Fintype.expect_eq_sum_div_card]
  simp only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast,
    mul_assoc, ← Finset.mul_sum]
  rw [mul_div_cancel_left₀ _ hcard]
  change (∑ b, (finiteImageMass p F b : ℂ) * test b) = _
  simp_rw [hmass]
  exact p.fiberLaw_complexMean F test

theorem rationalOutputDensity_divisor_test {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    (test : (J → ZMod q) → ℂ) :
    (𝔼 b : J → ZMod N, (rationalOutputDensity p Y N b : ℂ) *
      test (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      p.complexMean (fun x => test (fun j => (Y x j : ZMod q))) := by
  simpa only [map_intCast] using rationalOutputDensity_test p Y N
    (fun b => test (fun j => ZMod.castHom hq (ZMod q) (b j)))

theorem rationalOutputDensity_fourier {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) :
    (rationalOutputDensity p Y N b : ℂ) =
      ∑ χ : AddChar (J → ZMod N) ℂ,
        finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b) := by
  simpa only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast] using
    (finiteImageFourier_inversion p (fun x j => (Y x j : ZMod N)) b).symm

noncomputable def rationalInactiveForecast {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (b : J → ZMod N) : ℝ :=
  gridVolume * inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b)

theorem rationalInactiveForecast_nonneg {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : 0 ≤ gridVolume) (z : Z) (b : J → ZMod N) :
    0 ≤ rationalInactiveForecast inactive active gridPoint Y N gridVolume z b :=
  mul_nonneg hV (inactive.fiberMean_nonneg gridPoint z _
    (fun i => rationalOutputDensity_nonneg (active i) (Y i) N b))

theorem rationalInactiveForecast_divisor_test {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype Z] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑ z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (active i).complexMean
        (fun a => test (gridPoint i) (fun j => (Y i a j : ZMod q)))) := by
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  rw [← Finset.expect_sum_comm]
  have hswap (b : J → ZMod N) :
      (∑ z, (inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i) (fun j => ZMod.castHom hq (ZMod q) (b j))) :=
    (inactive.complexMean_fiber_factor gridPoint _ _).symm
  simp_rw [hswap]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalOutputDensity_divisor_test (active i) (Y i) hq]
  rfl

theorem rationalOutputDensity_complexMean_one {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N] :
    (𝔼 b : J → ZMod N, (rationalOutputDensity p Y N b : ℂ)) = 1 := by
  simpa only [mul_one, FiniteProbabilityWeights.complexMean_const] using
    rationalOutputDensity_test p Y N (fun _ => 1)

theorem rationalInactiveForecast_complexMass_one {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype Z] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) :
    (∑ z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b /
        gridVolume : ℝ) : ℂ)) = 1 := by
  simpa only [mul_one, FiniteProbabilityWeights.complexMean_const] using
    rationalInactiveForecast_divisor_test inactive active gridPoint Y (dvd_refl N) hV (fun _ _ => 1)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalOutputDensity_le_modulus_pow
    {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]
    (law : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    (b : J → ZMod N) :
    rationalOutputDensity law Y N b ≤ (N : ℝ) ^ Fintype.card J := by
  have hmass : finiteImageMass law (fun x j => (Y x j : ZMod N)) b ≤ 1 := by
    unfold finiteImageMass
    calc
      _ ≤ law.mean (fun _ => 1) := law.mean_mono (fun _ => by split_ifs <;> norm_num)
      _ = 1 := law.mean_const 1
  unfold rationalOutputDensity
  calc
    _ ≤ (Fintype.card (J → ZMod N) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg _)
    _ = _ := by simp only [Fintype.card_fun, ZMod.card, Nat.cast_pow, mul_one]

theorem rationalInactiveForecast_le_grid_mass_modulus_pow
    {I A Z J : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {volume : ℝ} (hV : 0 ≤ volume) (z : Z) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N volume z b ≤
      volume * inactive.fiberMean gridPoint z (fun _ => 1) *
        (N : ℝ) ^ Fintype.card J := by
  unfold rationalInactiveForecast FiniteProbabilityWeights.fiberMean
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hV
  unfold FiniteProbabilityWeights.mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gridPoint i = z
  · simp only [hi, ite_true, mul_one]
    exact mul_le_mul_of_nonneg_left
      (rationalOutputDensity_le_modulus_pow (active i) (Y i) N b) (inactive.nonneg i)
  · simp only [hi, ite_false, mul_zero, zero_mul, le_refl]

theorem rationalInactiveForecast_le_exp_of_grid_modulus
    {I A Z J : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {volume Pgrid Pmod : ℝ} (hV : 0 ≤ volume)
    (hgrid : ∀ z, volume * inactive.fiberMean gridPoint z (fun _ => 1) ≤ Real.exp Pgrid)
    (hN : (N : ℝ) ≤ Real.exp Pmod) (z : Z) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N volume z b ≤
      Real.exp (Pgrid + (Fintype.card J : ℝ) * Pmod) := by
  calc
    _ ≤ volume * inactive.fiberMean gridPoint z (fun _ => 1) *
        (N : ℝ) ^ Fintype.card J :=
      rationalInactiveForecast_le_grid_mass_modulus_pow inactive active gridPoint Y N hV z b
    _ ≤ Real.exp Pgrid * (Real.exp Pmod) ^ Fintype.card J :=
      mul_le_mul (hgrid z) (pow_le_pow_left₀ (Nat.cast_nonneg _) hN _)
        (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {Ω J : Type*} [Fintype Ω] [Fintype J] [DecidableEq J]

def integerResidueTuple (N : ℕ) : (J → ℤ) →+ (J → ZMod N) where
  toFun x j := (x j : ZMod N)
  map_zero' := by ext j; simp
  map_add' := by intro x y; ext j; simp

omit [Fintype J] [DecidableEq J] in
theorem integerResidueTuple_surjective (N : ℕ) :
    Function.Surjective (integerResidueTuple (J := J) N) := by
  intro y
  choose x hx using fun j => ZMod.intCast_surjective (y j)
  exact ⟨x, funext hx⟩

theorem rationalOutputDensity_order_bounds
    (p : FiniteProbabilityWeights Ω) (Y : Ω → J → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (J → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) :
    let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
    (∀ b, rationalOutputDensity p Y N b ≤ 1 + C) ∧
    S.card ≤ T ^ (Fintype.card J + 1) ∧
    (∑ χ ∈ S, ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖) ≤
      (T : ℝ) ^ (Fintype.card J + 1) ∧
    ∀ b, ‖(rationalOutputDensity p Y N b : ℂ) -
      ∑ χ ∈ S, finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)‖
        ≤ C / T := by
  have hd := finiteCharacter_integer_decay_of_rpow (I := J) hC hP _ hdecay
  let π := integerResidueTuple (J := J) N
  have hπ : Function.Surjective π := integerResidueTuple_surjective N
  refine ⟨fun b => finiteImage_density_bound_of_order_decay π hπ p _ hC hd b,
    finiteCharacter_boundedOrder_card_le π hπ T,
    finiteImage_boundedOrder_coefficient_mass π hπ p _ T, ?_⟩
  intro b
  simpa only [rationalOutputDensity, Complex.ofReal_mul, Complex.ofReal_natCast] using
    finiteImage_density_order_truncation π hπ p _ hC hd T hT b

theorem rationalInactiveForecast_cap {I A Z : Type*} [Fintype I] [Fintype A]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (z : Z) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (1 + C) := by
  have hcap (i) := (rationalOutputDensity_order_bounds (active i) (Y i) N hC hP
    (hdecay i) 1 zero_lt_one).1 b
  unfold rationalInactiveForecast FiniteProbabilityWeights.fiberMean
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hV
  unfold FiniteProbabilityWeights.mean
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : gridPoint i = z
  · simp only [hi, ite_true, mul_one]
    exact mul_le_mul_of_nonneg_left (hcap i) (inactive.nonneg i)
  · simp only [hi, ite_false, mul_zero, zero_mul, le_refl]

theorem rationalInactiveForecast_order_truncation {I A Z : Type*} [Fintype I] [Fintype A]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) (z : Z) (b : J → ZMod N) :
    let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
    ‖(rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) -
      (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active i)
          (fun x j => (Y i x j : ZMod N)) χ * star (χ b) else 0)‖ ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (C / T) := by
  let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
  let trunc (i : I) : ℂ := ∑ χ ∈ S, finiteImageCharacteristic (active i)
    (fun x j => (Y i x j : ZMod N)) χ * star (χ b)
  have heq : (rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) =
      (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
        (rationalOutputDensity (active i) (Y i) N b : ℂ) else 0) := by
    unfold rationalInactiveForecast FiniteProbabilityWeights.fiberMean
    rw [Complex.ofReal_mul, ← inactive.complexMean_ofReal]
    congr 2
    funext i
    split_ifs <;> rfl
  change ‖_ - (gridVolume : ℂ) * inactive.complexMean
    (fun i => if gridPoint i = z then trunc i else 0)‖ ≤ _
  rw [heq, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hV, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hV
  calc
    _ ≤ inactive.mean (fun i => if gridPoint i = z then C / T else 0) := by
      apply inactive.norm_complexMean_sub_le
      intro i _
      by_cases hi : gridPoint i = z
      · simp only [hi, ite_true]
        exact (rationalOutputDensity_order_bounds (active i) (Y i) N hC hP
          (hdecay i) T hT).2.2.2 b
      · simp only [hi, ite_false, sub_self, norm_zero, le_refl]
    _ = _ := by
      unfold FiniteProbabilityWeights.fiberMean FiniteProbabilityWeights.mean
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : gridPoint i = z <;> simp [hi]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]
variable (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
variable {N : ℕ} [NeZero N] (qW : ℕ) (hW : qW ∣ N)
variable (aux : Aux → ZMod N)
variable (g : ((V → ℝ) × (J → ℝ)) → ℝ)
variable (φ : (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
variable (hg : Continuous g) (hφ : ∀ b, Continuous (φ b))
variable (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0)

local notation "Domain" => (V → ℝ) × (J → ℝ)
local notation "rout" => rationalOutputDensity p Y N

include hg hφ hsupport

theorem rationalOutput_gridTest_integrable (b : J → ZMod qW) :
    Integrable (fun x : Domain => (g x : ℂ) * φ b x)
      ((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  apply ((Complex.continuous_ofReal.comp hg).mul (hφ b)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Domain) R)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra! hn
  apply hx
  change (g x : ℂ) * φ b x = 0
  rw [hsupport x hn, Complex.ofReal_zero, zero_mul]

include hW in
theorem rationalOutput_partial_grid_integrable
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) :
    Integrable (fun c : V → ℝ =>
      (∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (rout (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ)) := by
  let fN := fun (b : J → ZMod N) (x : Domain) =>
    (g x : ℂ) * (rout (Sum.elim aux b) : ℂ) * φ (zmodPiReduction hW b) x
  have hfN (b : J → ZMod N) : Continuous (fN b) :=
    ((Complex.continuous_ofReal.comp hg).mul continuous_const).mul (hφ _)
  have hsN (b : J → ZMod N) (x : Domain) (hx : R < ‖x‖) : fN b x = 0 := by
    simp only [fN, hsupport x hx, Complex.ofReal_zero, zero_mul]
  have hred (k : J → ℤ) :
      zmodPiReduction hW (fun j => (k j : ZMod N)) =
        (fun j => (k j : ZMod qW)) := by
    funext j
    exact map_intCast (ZMod.castHom hW (ZMod qW)) (k j)
  simpa only [fN, hred] using translatedPartialPeriodicIntegerGrid_integrable
    N fN hfN center T hT R hsN

theorem rationalOutput_partial_reference_integrable :
    Integrable (fun c : V → ℝ => 𝔼 b : J → ZMod N,
      (rout (Sum.elim aux b) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x)) := by
  simp only [Finset.expect_eq_sum_div_card]
  apply Integrable.div_const
  apply integrable_finsetSum
  intro b _
  exact (rationalOutput_gridTest_integrable qW g φ hg hφ R hsupport
    (zmodPiReduction hW b)).integral_prod_left.const_mul _

theorem rationalOutput_partial_reference_integral :
    (∫ c : V → ℝ, 𝔼 b : J → ZMod N,
      (rout (Sum.elim aux b) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x)) =
      𝔼 b : J → ZMod N, (rout (Sum.elim aux b) : ℂ) *
        ∫ x : Domain, (g x : ℂ) * φ (zmodPiReduction hW b) x
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  have hi (b : J → ZMod N) := rationalOutput_gridTest_integrable qW g φ hg hφ R hsupport
    (zmodPiReduction hW b)
  simp only [Finset.expect_eq_sum_div_card]
  rw [integral_div, integral_finsetSum _
    (fun b _ => (hi b).integral_prod_left.const_mul (rout (Sum.elim aux b) : ℂ))]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_const_mul, ← integral_prod _ (hi b)]

theorem rationalOutput_partial_grid_sub_reference_integral
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) :
    (∫ c : V → ℝ,
      ((∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (rout (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N, (rout (Sum.elim aux b) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x))) =
      (∫ c : V → ℝ,
        (∑' k : J → ℤ,
          (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
          (rout (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
          φ (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
          ((∏ j, T j : ℝ) : ℂ)) -
      𝔼 b : J → ZMod N, (rout (Sum.elim aux b) : ℂ) *
        ∫ x : Domain, (g x : ℂ) * φ (zmodPiReduction hW b) x
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  rw [integral_sub
    (rationalOutput_partial_grid_integrable p Y qW hW aux g φ hg hφ R hsupport center T hT)
    (rationalOutput_partial_reference_integrable p Y qW hW aux g φ hg hφ R hsupport),
    rationalOutput_partial_reference_integral p Y qW hW aux g φ hg hφ R hsupport]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_order_truncation_separated
    {I A J Z : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J] [DecidableEq Z]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) (z : Z) (b : J → ZMod N) :
    let S := Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T)
    ‖(rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) -
      ∑ χ : S, (gridVolume : ℂ) * inactive.complexMean (fun i =>
        finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
          (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b)‖ ≤
      gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (C / T) := by
  intro S
  have h := rationalInactiveForecast_order_truncation inactive active gridPoint Y N hV hC hP
    hdecay T hT z b
  dsimp only at h
  have hi (i : I) :
      (if gridPoint i = z then
        ∑ χ ∈ S, finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ *
          star (χ b) else 0) =
      ∑ χ : S, (finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
        (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b) := by
    by_cases hz : gridPoint i = z
    · simp only [hz, ite_true, mul_one]
      exact Finset.sum_subtype S (fun _ => Iff.rfl) _
    · simp only [hz, ite_false, mul_zero, zero_mul, Finset.sum_const_zero]
  have hsep : (gridVolume : ℂ) * inactive.complexMean (fun i => if gridPoint i = z then
      ∑ χ ∈ S, finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ *
        star (χ b) else 0) =
      ∑ χ : S, (gridVolume : ℂ) * inactive.complexMean (fun i =>
        finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
          (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b) := by
    simp_rw [hi]
    unfold FiniteProbabilityWeights.complexMean
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [← hsep]
  convert h using 1
  congr 4
  funext i
  split_ifs <;> rfl

theorem rationalInactiveForecast_retained_approximation
    {I A J Z : Type*} [Fintype I] [Fintype A] [Fintype J] [DecidableEq J] [DecidableEq Z]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume C P err : ℝ} (hV : 0 ≤ gridVolume) (hC : 0 ≤ C)
    (hP : ((Fintype.card J + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ i (χ : AddChar (J → ZMod N) ℂ),
      ‖finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P))
    (T : ℕ) (hT : 0 < T) (z : Z) (b : J → ZMod N) (model : ℂ)
    (hret :
      ‖(∑ χ : Finset.univ.filter (fun χ : AddChar (J → ZMod N) ℂ => orderOf χ ≤ T),
        (gridVolume : ℂ) * inactive.complexMean (fun i =>
          finiteImageCharacteristic (active i) (fun x j => (Y i x j : ZMod N)) χ.val *
          (if gridPoint i = z then (1 : ℂ) else 0)) * star (χ.val b)) - model‖ ≤ err) :
      ‖(rationalInactiveForecast inactive active gridPoint Y N gridVolume z b : ℂ) - model‖ ≤
        gridVolume * inactive.fiberMean gridPoint z (fun _ => 1) * (C / T) + err := by
  have htail := rationalInactiveForecast_order_truncation_separated inactive active gridPoint Y N
    hV hC hP hdecay T hT z b
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add htail hret)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem compactGrid_summable {J : Type*} [Fintype J]
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    Summable (fun k : J → ℤ => g (fun j => ((k j : ℝ) - center j) / scale j)) := by
  have h := rectangularWeight_summable g center scale hscale hsupport
  unfold rectangularWeight rectangularLatticePoint at h
  simpa only [Pi.zero_apply, sub_zero] using h

theorem compactGrid_weighted_summable {J : Type*} [Fintype J]
    (g : (J → ℝ) → ℝ) (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j)
    (R : ℝ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) (mask : (J → ℤ) → ℂ) :
    Summable (fun k : J → ℤ => (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) * mask k) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rectangularWeightIndices center scale R) ?_).summable
  intro k hk
  have h := rectangularWeight_zero_off_indices g center scale hscale hsupport k hk
  unfold rectangularWeight rectangularLatticePoint at h
  rw [h, Complex.ofReal_zero, zero_mul]

variable {Ω O : Type*} [Fintype Ω] [Fintype O] [DecidableEq O]

noncomputable def rationalOutputOrderTail
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    (T : ℕ) (b : O → ZMod N) : ℂ :=
  (rationalOutputDensity p Y N b : ℂ) -
    ∑ χ ∈ Finset.univ.filter (fun χ : AddChar (O → ZMod N) ℂ => orderOf χ ≤ T),
      finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)

theorem rationalOutputOrderTail_norm_le
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T) (b : O → ZMod N) :
    ‖rationalOutputOrderTail p Y N T b‖ ≤ C / T :=
  (rationalOutputDensity_order_bounds p Y N hC hP hdecay T hT).2.2.2 b

theorem rationalOutputOrderTail_weighted_norm_le
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (b : O → ZMod N) (w : ℝ) (hw : 0 ≤ w) (φ : ℂ) (hφ : ‖φ‖ ≤ 1) :
    ‖(w : ℂ) * rationalOutputOrderTail p Y N T b * φ‖ ≤ (C / T) * w := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  calc
    _ ≤ w * ‖rationalOutputOrderTail p Y N T b‖ * 1 :=
      mul_le_mul_of_nonneg_left hφ (mul_nonneg hw (norm_nonneg _))
    _ ≤ w * (C / T) := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left
        (rationalOutputOrderTail_norm_le p Y N hC hP hdecay T hT b) hw
    _ = _ := mul_comm _ _

theorem rationalOutputOrderTail_weighted_tsum_le {K : Type*}
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (w : K → ℝ) (hw : ∀ k, 0 ≤ w k) (hws : Summable w)
    (b : K → O → ZMod N) (φ : K → ℂ) (hφ : ∀ k, ‖φ k‖ ≤ 1) :
    ‖∑' k, (w k : ℂ) * rationalOutputOrderTail p Y N T (b k) * φ k‖ ≤
      (C / T) * ∑' k, w k := by
  exact tsum_of_norm_bounded (hws.hasSum.mul_left (C / T)) (fun k =>
    rationalOutputOrderTail_weighted_norm_le p Y N hC hP hdecay T hT
      (b k) (w k) (hw k) (φ k) (hφ k))

theorem rationalOutputOrderTail_grid_le {J : Type*} [Fintype J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : (J → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (φ : (J → ℤ) → ℂ)
    (hφ : ∀ k, ‖φ k‖ ≤ 1) :
    ‖∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      rationalOutputOrderTail p Y N T (b k) * φ k‖ / (∏ j, scale j) ≤
      (C / T) * ((∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / scale j)) /
        (∏ j, scale j)) := by
  have hs := compactGrid_summable g center scale hscale R hsupport
  have h := rationalOutputOrderTail_weighted_tsum_le p Y N hC hP hdecay T hT
    (fun k : J → ℤ => g (fun j => ((k j : ℝ) - center j) / scale j)) (fun k => hg _) hs b φ hφ
  have hd : 0 < ∏ j, scale j := Finset.prod_pos (fun j _ => hscale j)
  exact (div_le_div_of_nonneg_right h hd.le).trans_eq (by ring)

theorem rationalOutputOrderTail_integral_le {X : Type*} [MeasurableSpace X]
    (μ : Measure X)
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g μ)
    (b : X → O → ZMod N) (φ : X → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1) :
    ‖∫ x, (g x : ℂ) * rationalOutputOrderTail p Y N T (b x) * φ x ∂μ‖ ≤
      (C / T) * ∫ x, g x ∂μ := by
  calc
    _ ≤ ∫ x, (C / T) * g x ∂μ :=
      norm_integral_le_of_norm_le (hgi.const_mul (C / T))
        (Filter.Eventually.of_forall (fun x =>
          rationalOutputOrderTail_weighted_norm_le p Y N hC hP hdecay T hT
            (b x) (g x) (hg x) (φ x) (hφ x)))
    _ = _ := integral_const_mul _ _

theorem rationalOutputOrderTail_normalized_grid_le {J : Type*} [Fintype J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : (J → ℝ) → ℝ) (hg : ∀ x, 0 ≤ g x)
    (center scale : J → ℝ) (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (φ : (J → ℤ) → ℂ)
    (hφ : ∀ k, ‖φ k‖ ≤ 1) :
    ‖(∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      rationalOutputOrderTail p Y N T (b k) * φ k) / ((∏ j, scale j : ℝ) : ℂ)‖ ≤
      (C / T) * ((∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / scale j)) /
        (∏ j, scale j)) := by
  have hd : 0 < ∏ j, scale j := Finset.prod_pos (fun j _ => hscale j)
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hd.le]
  exact rationalOutputOrderTail_grid_le p Y N hC hP hdecay T hT
    g hg center scale hscale R hsupport b φ hφ

theorem rationalOutputOrderTail_mean_integral_le
    {X K : Type*} [MeasurableSpace X] [Fintype K] [Nonempty K]
    (μ : Measure X)
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    {C P : ℝ} (hC : 0 ≤ C) (hP : ((Fintype.card O + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar (O → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        C * (orderOf χ : ℝ) ^ (-P)) (T : ℕ) (hT : 0 < T)
    (g : X → ℝ) (hg : ∀ x, 0 ≤ g x) (hgi : Integrable g μ)
    (b : K → O → ZMod N) (φ : K → X → ℂ) (hφ : ∀ k x, ‖φ k x‖ ≤ 1) :
    ‖𝔼 k : K, rationalOutputOrderTail p Y N T (b k) *
      ∫ x, (g x : ℂ) * φ k x ∂μ‖ ≤ (C / T) * ∫ x, g x ∂μ := by
  have hnorm (k : K) : ‖∫ x, (g x : ℂ) * φ k x ∂μ‖ ≤ ∫ x, g x ∂μ := by
    apply norm_integral_le_of_norm_le hgi
    filter_upwards [] with x
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hg x)]
    exact (mul_le_mul_of_nonneg_left (hφ k x) (hg x)).trans_eq (mul_one _)
  have hpoint (k : K) :
      ‖rationalOutputOrderTail p Y N T (b k) * ∫ x, (g x : ℂ) * φ k x ∂μ‖ ≤
        (C / T) * ∫ x, g x ∂μ := by
    rw [norm_mul]
    exact mul_le_mul (rationalOutputOrderTail_norm_le p Y N hC hP hdecay T hT (b k))
      (hnorm k) (norm_nonneg _) (div_nonneg hC (Nat.cast_nonneg _))
  let law := FiniteProbabilityWeights.uniform K
  have h := (law.norm_complexMean_le_mean_norm _).trans (law.mean_mono hpoint)
  simpa only [law, FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.mean_const] using h

theorem rationalOutputOrderTail_grid_difference {J : Type*} [Fintype J]
    (p : FiniteProbabilityWeights Ω) (Y : Ω → O → ℤ) (N : ℕ) [NeZero N]
    (T : ℕ) (g : (J → ℝ) → ℝ) (center scale : J → ℝ)
    (hscale : ∀ j, 0 < scale j) (R : ℝ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0)
    (b : (J → ℤ) → O → ZMod N) (φ : (J → ℤ) → ℂ) :
    let S := Finset.univ.filter (fun χ : AddChar (O → ZMod N) ℂ => orderOf χ ≤ T)
    (∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      rationalOutputOrderTail p Y N T (b k) * φ k) / ((∏ j, scale j : ℝ) : ℂ) =
    (∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      (rationalOutputDensity p Y N (b k) : ℂ) * φ k) / ((∏ j, scale j : ℝ) : ℂ) -
    (∑' k : J → ℤ, (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) *
      (∑ χ ∈ S, finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ *
        star (χ (b k))) * φ k) / ((∏ j, scale j : ℝ) : ℂ) := by
  intro S
  let full := fun k : J → ℤ => (rationalOutputDensity p Y N (b k) : ℂ)
  let trunc := fun k : J → ℤ => ∑ χ ∈ S,
    finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ (b k))
  have hfull : Summable (fun k : J → ℤ =>
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) * full k * φ k) := by
    simpa only [mul_assoc] using compactGrid_weighted_summable
      g center scale hscale R hsupport (fun k => full k * φ k)
  have htrunc : Summable (fun k : J → ℤ =>
      (g (fun j => ((k j : ℝ) - center j) / scale j) : ℂ) * trunc k * φ k) := by
    simpa only [mul_assoc] using compactGrid_weighted_summable
      g center scale hscale R hsupport (fun k => trunc k * φ k)
  rw [← sub_div, ← hfull.tsum_sub htrunc]
  congr 1
  apply tsum_congr
  intro k
  change _ * (full k - trunc k) * φ k = _
  ring

end Erdos3

end

end OAI
