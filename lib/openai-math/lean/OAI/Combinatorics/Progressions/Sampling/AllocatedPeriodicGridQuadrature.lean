import OAI.Combinatorics.Progressions.Estimates.CompactSliceErrorIntegral
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTsum
import OAI.Combinatorics.Progressions.Fourier.RationalCharacterIndividualModulus
import OAI.Combinatorics.Progressions.Fourier.RetainedCharacterGridSum
import OAI.Combinatorics.Progressions.Lattices.ForecastIntegerAxisSplit
import OAI.Combinatorics.Progressions.Lattices.IntegerResidueLatticeSum
import OAI.Combinatorics.Progressions.Probability.ComplexDensityScaledQuadrature

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators NNReal
variable {J : Type*} [Fintype J]

noncomputable def translatedGridMass (g : (J → ℝ) → ℝ) (center T : J → ℝ) : ℝ :=
  (∑' k : J → ℤ, g (fun j => ((k j : ℝ) - center j) / T j)) / (∏ j, T j)

theorem translatedGridMass_nonneg (g : (J → ℝ) → ℝ) (center T : J → ℝ)
    (hg : ∀ x, 0 ≤ g x) (hT : ∀ j, 0 < T j) :
    0 ≤ translatedGridMass g center T :=
  div_nonneg (tsum_nonneg (fun _ => hg _)) (Finset.prod_nonneg (fun j _ => (hT j).le))

theorem translatedGridMass_error (g : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L g) (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, 1 / T j ≤ δ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    |translatedGridMass g center T - ∫ x, g x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ :=
  rectangularLattice_quadrature g hLip center T hT hR hδ hδ1 hmesh hsupport

theorem translatedGridMass_le (g : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L g) (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, 1 / T j ≤ δ) (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    translatedGridMass g center T ≤ (∫ x, g x) +
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have h := (le_abs_self _).trans (translatedGridMass_error g hLip center T hT
    hR hδ hδ1 hmesh hsupport)
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem rationalInactiveForecast_zero_off_image {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    (gridVolume : ℝ) (z : Z) (hz : z ∉ Finset.univ.image gridPoint) (b : J → ZMod N) :
    rationalInactiveForecast inactive active gridPoint Y N gridVolume z b = 0 := by
  rw [rationalInactiveForecast,
    inactive.fiberMean_eq_zero_of_not_mem_image gridPoint _ z hz, mul_zero]

theorem rationalInactiveForecast_divisor_test_summable {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    (gridVolume : ℝ) (test : Z → (J → ZMod q) → ℂ) :
    Summable (fun z => 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))) := by
  apply (hasSum_sum_of_ne_finset_zero (s := Finset.univ.image gridPoint) ?_).summable
  intro z hz
  simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
    zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero]

theorem rationalInactiveForecast_divisor_tsum_test {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (active i).complexMean
        (fun a => test (gridPoint i) (fun j => (Y i a j : ZMod q)))) := by
  classical
  rw [tsum_eq_sum (s := Finset.univ.image gridPoint) (fun z hz => by
    simp only [rationalInactiveForecast_zero_off_image inactive active gridPoint Y N gridVolume z hz,
      zero_div, Complex.ofReal_zero, zero_mul, Finset.expect_const_zero])]
  simp only [rationalInactiveForecast, mul_div_cancel_left₀ _ hV]
  rw [← Finset.expect_sum_comm]
  have hswap (b : J → ZMod N) :
      (∑ z ∈ Finset.univ.image gridPoint,
        (inactive.fiberMean gridPoint z (fun i => rationalOutputDensity (active i) (Y i) N b) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => (rationalOutputDensity (active i) (Y i) N b : ℂ) *
        test (gridPoint i) (fun j => ZMod.castHom hq (ZMod q) (b j))) :=
    (inactive.complexMean_fiber_factor_sum_image gridPoint _ _).symm
  simp_rw [hswap]
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect]
  apply Finset.sum_congr rfl
  intro i _
  rw [rationalOutputDensity_divisor_test (active i) (Y i) hq]
  rfl

theorem rationalInactivePolynomialForecast_tsum_marginal
    {Ω A I J Z : Type*} [Fintype Ω] [Fintype A] [DecidableEq A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights Ω) (gridPoint : Ω → Z)
    (poly : J → MvPolynomial (A ⊕ I) ℤ) (inactiveCoord : Ω → I → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ) :
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive
        (fun _ => FiniteProbabilityWeights.uniform (A → ZMod N)) gridPoint
        (fun i => integerLongPolynomialOutput poly (inactiveCoord i) N)
        N gridVolume z b / gridVolume : ℝ) : ℂ) *
          test z (fun j => ZMod.castHom hq (ZMod q) (b j))) =
      inactive.complexMean (fun i => 𝔼 t : A → ZMod q,
        test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
          (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j))) := by
  rw [rationalInactiveForecast_divisor_tsum_test _ _ _ _ hq hV]
  congr 1
  funext i
  rw [FiniteProbabilityWeights.uniform_complexMean]
  simp_rw [integerLongPolynomialOutput_reduce poly (inactiveCoord i) hq]
  exact uniform_residue_reduction_complexMean (A := A) (q := q) (N := N) hq
    (fun t => test (gridPoint i) (fun j => MvPolynomial.eval₂ (Int.castRingHom (ZMod q))
      (Sum.elim t (fun a => (inactiveCoord i a : ZMod q))) (poly j)))

theorem rationalInactiveForecast_divisor_tsum_test_norm_le {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ)
    {q N : ℕ} [NeZero N] [NeZero q] (hq : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) (test : Z → (J → ZMod q) → ℂ)
    (htest : ∀ z b, ‖test z b‖ ≤ 1) :
    ‖∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        test z (fun j => ZMod.castHom hq (ZMod q) (b j))‖ ≤ 1 := by
  rw [rationalInactiveForecast_divisor_tsum_test inactive active gridPoint Y hq hV test]
  apply (inactive.norm_complexMean_le_mean_norm _).trans
  apply (inactive.mean_mono ?_).trans_eq (inactive.mean_const 1)
  intro i
  exact ((active i).norm_complexMean_le_mean_norm _).trans
    (((active i).mean_mono (fun a => htest _ _)).trans_eq ((active i).mean_const 1))

theorem rationalInactiveForecast_complexTsumMass_one {I A Z J : Type*}
    [Fintype I] [Fintype A] [Fintype J] [DecidableEq J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → J → ℤ) (N : ℕ) [NeZero N]
    {gridVolume : ℝ} (hV : gridVolume ≠ 0) :
    (∑' z, 𝔼 b : J → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ)) = 1 := by
  simpa only [mul_one, FiniteProbabilityWeights.complexMean_const] using
    rationalInactiveForecast_divisor_tsum_test inactive active gridPoint Y (dvd_refl N) hV (fun _ _ => 1)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

theorem periodicIntegerGrid_summable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → (J → ℝ) → ℂ)
    (T : J → ℝ) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Summable (fun k : J → ℤ => f (fun j => (k j : ZMod q)) (fun j => (k j : ℝ) / T j)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rectangularWeightIndices 0 T R) ?_).summable
  intro k hk
  have h := rectangularWeight_zero_off_indices
    (fun x => ‖f (fun j => (k j : ZMod q)) x‖) 0 T hT
    (fun x hx => by rw [hsupport _ x hx, norm_zero]) k hk
  change ‖f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - 0) / T j)‖ = 0 at h
  simpa only [sub_zero] using norm_eq_zero.mp h

theorem periodicIntegerGrid_complex_quadrature (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : ∀ r, LipschitzWith L (f r)) (T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (q : ℝ) / T j ≤ δ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    ‖(∑' k : J → ℤ, f (fun j => (k j : ZMod q)) (fun j => (k j : ℝ) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) - 𝔼 r : J → ZMod q, ∫ x, f r x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  let disc := fun r : J → ZMod q =>
    (((q : ℝ) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
      ∑' k : J → ℤ, f r (fun j => ((r j).val + (q : ℝ) * k j) / T j)
  let cont := fun r : J → ZMod q => ∫ x, f r x
  have havg := (FiniteProbabilityWeights.uniform (J → ZMod q)).norm_complexMean_sub_le
    disc cont (fun _ => 2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)
    (fun r _ => scaledRectangular_complex_quadrature _ (hLip r) _ T
      (Nat.cast_pos.mpr (NeZero.pos q)) hT hR hδ hδ1 hmesh (hsupport r))
  rw [FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.mean_const] at havg
  have hsum := tsum_integerResidueLatticePoint q
    (fun k : J → ℤ => f (fun j => (k j : ZMod q)) (fun j => (k j : ℝ) / T j))
    (periodicIntegerGrid_summable q f T hT hsupport)
  have hcast (r : J → ZMod q) (k : J → ℤ) :
      (fun j => (integerResidueLatticePoint q r k j : ZMod q)) = r := by
    funext j
    exact integerResidueLatticePoint_cast q r k j
  simp_rw [hcast] at hsum
  simp only [integerResidueLatticePoint, Int.cast_add, Int.cast_natCast, Int.cast_mul] at hsum
  have he : (𝔼 r : J → ZMod q, disc r) =
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q)) (fun j => (k j : ℝ) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) := by
    rw [hsum]
    simp only [Finset.expect_eq_sum_div_card, disc, ← Finset.mul_sum,
      Finset.card_univ, Fintype.card_fun, ZMod.card]
    push_cast
    have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  rw [he] at havg
  exact havg

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem rationalInactiveForecast_complex_grid_quadrature
    {I A Z O J : Type*} [Fintype I] [Fintype A] [Fintype O] [DecidableEq O] [Fintype J]
    (inactive : FiniteProbabilityWeights I) (active : I → FiniteProbabilityWeights A)
    (gridPoint : I → Z) (Y : I → A → O → ℤ)
    {q N : ℕ} [NeZero q] [NeZero N] (hqN : q ∣ N)
    {gridVolume : ℝ} (hV : gridVolume ≠ 0)
    (f : Z → (O → ZMod q) → (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : ∀ z r, LipschitzWith L (f z r))
    (c : Z → (O → ZMod q) → J → ℝ) (T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (q : ℝ) / T j ≤ δ)
    (hsupport : ∀ z r y, R < ‖y‖ → f z r y = 0) :
    ‖(∑' z, 𝔼 b : O → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
          (((q : ℝ) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
          ∑' k : J → ℤ, f z (fun j => ZMod.castHom hqN (ZMod q) (b j))
            (fun j => (c z (fun o => ZMod.castHom hqN (ZMod q) (b o)) j + q * k j) / T j)) -
      (∑' z, 𝔼 b : O → ZMod N,
        ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
          ∫ y, f z (fun j => ZMod.castHom hqN (ZMod q) (b j)) y)‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  let disc := fun z r => (((q : ℝ) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
    ∑' k : J → ℤ, f z r (fun j => (c z r j + q * k j) / T j)
  let cont := fun z r => ∫ y, f z r y
  have hd := rationalInactiveForecast_divisor_tsum_test inactive active gridPoint Y hqN hV disc
  have hc := rationalInactiveForecast_divisor_tsum_test inactive active gridPoint Y hqN hV cont
  have he : (∑' z, 𝔼 b : O → ZMod N,
      ((rationalInactiveForecast inactive active gridPoint Y N gridVolume z b / gridVolume : ℝ) : ℂ) *
        (((q : ℝ) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
        ∑' k : J → ℤ, f z (fun j => ZMod.castHom hqN (ZMod q) (b j))
          (fun j => (c z (fun o => ZMod.castHom hqN (ZMod q) (b o)) j + q * k j) / T j)) =
      inactive.complexMean (fun i => (active i).complexMean
        (fun a => disc (gridPoint i) (fun j => (Y i a j : ZMod q)))) := by
    simpa only [disc, mul_assoc] using hd
  rw [he, hc]
  apply (inactive.norm_complexMean_sub_le _ _
    (fun _ => 2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) ?_).trans_eq
      (inactive.mean_const _)
  intro i _
  apply ((active i).norm_complexMean_sub_le _ _
    (fun _ => 2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) ?_).trans_eq
      ((active i).mean_const _)
  intro a _
  exact scaledRectangular_complex_quadrature _ (hLip _ _) _ T
    (Nat.cast_pos.mpr (NeZero.pos q)) hT hR hδ hδ1 hmesh (hsupport _ _)

theorem retainedCharacter_complex_grid_quadrature
    {C J : Type*} [Fintype C] [Fintype J]
    (coeff : C → ℂ) (q : C → ℝ) (hq : ∀ a, 0 < q a)
    (f : C → (J → ℝ) → ℂ) (L : C → ℝ≥0) (hLip : ∀ a, LipschitzWith (L a) (f a))
    (c : C → J → ℝ) (T : J → ℝ) (hT : ∀ j, 0 < T j)
    (R δ : C → ℝ) (hR : ∀ a, 0 ≤ R a) (hδ : ∀ a, 0 ≤ δ a)
    (hδ1 : ∀ a, δ a ≤ 1) (hmesh : ∀ a j, q a / T j ≤ δ a)
    (hsupport : ∀ a y, R a < ‖y‖ → f a y = 0) :
    ‖(∑ a, coeff a * (((q a) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
        ∑' k : J → ℤ, f a (fun j => (c a j + q a * k j) / T j)) -
      ∑ a, coeff a * ∫ y, f a y‖ ≤
      ∑ a, ‖coeff a‖ * (2 * (2 * R a + 2) ^ Fintype.card J * (L a : ℝ) * δ a) := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [mul_assoc, ← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (scaledRectangular_complex_quadrature _ (hLip a) (c a) T (hq a) hT
      (hR a) (hδ a) (hδ1 a) (hmesh a) (hsupport a)) (norm_nonneg _)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

variable {J : Type*} [Fintype J]

theorem periodicTranslatedIntegerGrid_summable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → (J → ℝ) → ℂ)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) {R : ℝ}
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Summable (fun k : J → ℤ => f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)) := by
  apply (hasSum_sum_of_ne_finset_zero (s := rectangularWeightIndices center T R) ?_).summable
  intro k hk
  have h := rectangularWeight_zero_off_indices
    (fun x => ‖f (fun j => (k j : ZMod q)) x‖) center T hT
    (fun x hx => by rw [hsupport _ x hx, norm_zero]) k hk
  change ‖f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)‖ = 0 at h
  exact norm_eq_zero.mp h

theorem periodicTranslatedIntegerGrid_complex_quadrature (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → (J → ℝ) → ℂ) {L : ℝ≥0}
    (hLip : ∀ r, LipschitzWith L (f r)) (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (q : ℝ) / T j ≤ δ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    ‖(∑' k : J → ℤ, f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) - 𝔼 r : J → ZMod q, ∫ x, f r x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  let disc := fun r : J → ZMod q =>
    (((q : ℝ) ^ Fintype.card J / (∏ j, T j) : ℝ) : ℂ) *
      ∑' k : J → ℤ, f r (fun j => ((r j).val - center j + (q : ℝ) * k j) / T j)
  let cont := fun r : J → ZMod q => ∫ x, f r x
  have havg := (FiniteProbabilityWeights.uniform (J → ZMod q)).norm_complexMean_sub_le
    disc cont (fun _ => 2 * (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)
    (fun r _ => scaledRectangular_complex_quadrature _ (hLip r) _ T
      (Nat.cast_pos.mpr (NeZero.pos q)) hT hR hδ hδ1 hmesh (hsupport r))
  rw [FiniteProbabilityWeights.uniform_complexMean,
    FiniteProbabilityWeights.uniform_complexMean, FiniteProbabilityWeights.mean_const] at havg
  have hsum := tsum_integerResidueLatticePoint q
    (fun k : J → ℤ => f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j))
    (periodicTranslatedIntegerGrid_summable q f center T hT hsupport)
  have hcast (r : J → ZMod q) (k : J → ℤ) :
      (fun j => (integerResidueLatticePoint q r k j : ZMod q)) = r := by
    funext j
    exact integerResidueLatticePoint_cast q r k j
  simp_rw [hcast] at hsum
  simp only [integerResidueLatticePoint, Int.cast_add, Int.cast_natCast, Int.cast_mul, add_sub_right_comm] at hsum
  have he : (𝔼 r : J → ZMod q, disc r) =
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) := by
    rw [hsum]
    simp only [Finset.expect_eq_sum_div_card, disc, ← Finset.mul_sum,
      Finset.card_univ, Fintype.card_fun, ZMod.card]
    push_cast
    have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
    field_simp
  rw [he] at havg
  exact havg

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators Classical

private theorem constantPhase_density_test_lipschitz {X : Type*} [PseudoMetricSpace X]
    (phase : ℂ) (hphase : ‖phase‖ ≤ 1)
    (g : X → ℝ) (φ : X → ℂ) (C L K : ℝ≥0)
    (hg : LipschitzWith L g) (hφ : LipschitzWith K φ)
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    LipschitzWith (L + C * K) (fun x => phase * (g x : ℂ) * φ x) := by
  have h := density_complex_test_lipschitz g φ C L K hg hφ hcap hbound
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (phase * (g x : ℂ) * φ x) (phase * (g y : ℂ) * φ y) =
        ‖phase‖ * dist ((g x : ℂ) * φ x) ((g y : ℂ) * φ y) := by
      simp only [dist_eq_norm, mul_assoc, ← mul_sub, norm_mul]
    _ ≤ 1 * dist ((g x : ℂ) * φ x) ((g y : ℂ) * φ y) :=
      mul_le_mul_of_nonneg_right hphase (dist_nonneg)
    _ ≤ _ := by simpa only [one_mul] using h.dist_le_mul x y

variable {Aux J : Type*} [Fintype Aux] [Fintype J]

theorem retainedRationalCharacter_grid_quadrature
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (aux : Aux → ZMod N)
    (g : (J → ℝ) → ℝ) (φ : (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (rationalCharacterIndividualModulus qW χ : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' k : J → ℤ, star (χ (Sum.elim aux (fun j => (k j : ZMod N)))) *
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N, star (χ (Sum.elim aux b)) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x‖ ≤
      2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ := by
  let q := rationalCharacterIndividualModulus qW χ
  let ψ := rationalCharacterIndividualReduction qW χ hW
  let auxq : Aux → ZMod q := zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW) aux
  let f : (J → ZMod q) → (J → ℝ) → ℂ := fun b x =>
    star (ψ (Sum.elim auxq b)) * (g x : ℂ) *
      φ (zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ) b) x
  have hLip : ∀ b, LipschitzWith (L + C * K) (f b) := by
    intro b
    exact constantPhase_density_test_lipschitz _
      (by simp only [norm_star, AddChar.norm_apply, le_refl])
      g _ C L K hg (hφ _) hcap (hbound _)
  have hsupp : ∀ b x, R < ‖x‖ → f b x = 0 := by
    intro b x hx
    simp only [f, hsupport x hx, Complex.ofReal_zero, mul_zero, zero_mul]
  have h := periodicTranslatedIntegerGrid_complex_quadrature q f hLip center T hT
    hR hδ hδ1 hmesh hsupp
  have heval (k : J → ℤ) :
      f (fun j => (k j : ZMod q)) (fun j => ((k j : ℝ) - center j) / T j) =
        star (χ (Sum.elim aux (fun j => (k j : ZMod N)))) *
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j) := by
    have hp := rationalCharacterIndividualReduction_apply qW χ hW
      (Sum.elim aux (fun j => (k j : ZMod N)))
    have he : zmodPiReduction (rationalCharacterIndividualModulus_dvd qW χ hW)
        (Sum.elim aux (fun j => (k j : ZMod N))) =
        Sum.elim auxq (fun j => (k j : ZMod q)) := by
      funext j
      cases j <;> simp only [zmodPiReduction_apply, Sum.elim_inl, Sum.elim_inr,
        map_intCast, auxq]
    rw [he] at hp
    have htest : zmodPiReduction (rationalCharacterIndividualModulus_test_dvd qW χ)
        (fun j => (k j : ZMod q)) = (fun j => (k j : ZMod qW)) := by
      funext j
      exact map_intCast (ZMod.castHom (rationalCharacterIndividualModulus_test_dvd qW χ) (ZMod qW)) (k j)
    simp only [f, ψ, hp, htest]
  have havg : (𝔼 b : J → ZMod q, ∫ x, f b x) =
      𝔼 b : J → ZMod N, star (χ (Sum.elim aux b)) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x := by
    simp only [f, mul_assoc, integral_const_mul]
    exact (rationalCharacterIndividualReduction_partial_star_uniform qW hW χ aux
      (fun b => ∫ x, (g x : ℂ) * φ b x)).symm
  simpa only [heval, havg, NNReal.coe_add, NNReal.coe_mul] using h

theorem retainedRationalOutput_grid_quadrature
    {Ω : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω)
    (Y : Ω → (Aux ⊕ J) → ℤ)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ)
    (g : (J → ℝ) → ℝ) (φ : (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    let S := Finset.univ.filter
      (fun χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ => orderOf χ ≤ cutoff)
    let coeff := fun χ => finiteImageCharacteristic p (fun ω o => (Y ω o : ZMod N)) χ
    ‖(∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (∑ χ ∈ S, coeff χ * star (χ (Sum.elim aux (fun j => (k j : ZMod N))))) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N,
        (∑ χ ∈ S, coeff χ * star (χ (Sum.elim aux b))) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) := by
  let S := Finset.univ.filter
    (fun χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ => orderOf χ ≤ cutoff)
  let coeff := fun χ => finiteImageCharacteristic p (fun ω o => (Y ω o : ZMod N)) χ
  let grid : (J → ℤ) → J → ℝ := fun k j => ((k j : ℝ) - center j) / T j
  let phase := fun (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (k : J → ℤ) =>
    star (χ (Sum.elim aux (fun j => (k j : ZMod N))))
  let test := fun k : J → ℤ => φ (fun j => (k j : ZMod qW)) (grid k)
  let refPhase := fun (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (b : J → ZMod N) =>
    star (χ (Sum.elim aux b))
  let refTest := fun b : J → ZMod N => ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x
  let err : ℝ := 2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ
  have hs (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) :
      Summable (fun k : J → ℤ => phase χ k * (g (grid k) : ℂ) * test k) := by
    have hsum := periodicTranslatedIntegerGrid_summable (R := R) N
      (fun b x => star (χ (Sum.elim aux b)) * (g x : ℂ) * φ (zmodPiReduction hW b) x)
      center T hT (fun b x hx => by
        simp only [hsupport x hx, Complex.ofReal_zero, mul_zero, zero_mul])
    have hr (k : J → ℤ) : zmodPiReduction hW (fun j => (k j : ZMod N)) =
        (fun j => (k j : ZMod qW)) := by
      funext j
      exact map_intCast (ZMod.castHom hW (ZMod qW)) (k j)
    simpa only [hr] using hsum
  have hcoeff : (∑ χ ∈ S, ‖coeff χ‖) ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) :=
    finiteImage_boundedOrder_coefficient_mass
      (integerResidueTuple (J := Aux ⊕ J) N) (integerResidueTuple_surjective N)
      p (fun ω o => (Y ω o : ZMod N)) cutoff
  have he (χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ) (hχ : χ ∈ S) :
      ‖(∑' k, phase χ k * (g (grid k) : ℂ) * test k) / ((∏ j, T j : ℝ) : ℂ) -
        (𝔼 b, refPhase χ b * refTest b)‖ ≤ err := by
    have hm (j) : (rationalCharacterIndividualModulus qW χ : ℝ) / T j ≤ δ := by
      have hq := rationalCharacterIndividualModulus_le_mul qW χ (Finset.mem_filter.mp hχ).2
      exact (div_le_div_of_nonneg_right (Nat.cast_le.mpr hq) (hT j).le).trans (hmesh j)
    exact retainedRationalCharacter_grid_quadrature qW hW χ aux g φ C L K hg hφ
      hcap hbound center T hT hR hδ hδ1 hm hsupport
  exact retainedCharacterGrid_tsum_sub_expect_le S coeff
    (fun k => (g (grid k) : ℂ)) phase test ((∏ j, T j : ℝ) : ℂ)
    refPhase refTest (fun χ _ => hs χ) (by positivity) hcoeff he

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J : Type*} [Fintype Ω] [Fintype Aux] [Fintype J]

theorem rationalOutput_translated_grid_comparison
    (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : (J → ℝ) → ℝ) (φ : (J → ZMod qW) → (J → ℝ) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖(∑' k : J → ℤ,
        (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (rationalOutputDensity p Y N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N,
        (rationalOutputDensity p Y N (Sum.elim aux b) : ℂ) *
        ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x‖ ≤
      (cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
      (D / cutoff) * (2 * (∫ x, g x) +
        (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) := by
  classical
  let trunc := fun b : (Aux ⊕ J) → ZMod N =>
    ∑ χ ∈ Finset.univ.filter (fun χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ => orderOf χ ≤ cutoff),
      finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ * star (χ b)
  let raw := (∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      (rationalOutputDensity p Y N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
      φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ)
  let rawRet := (∑' k : J → ℤ,
      (g (fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      trunc (Sum.elim aux (fun j => (k j : ZMod N))) *
      φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ)
  let refRet := 𝔼 b : J → ZMod N, trunc (Sum.elim aux b) *
    ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x
  let ref := 𝔼 b : J → ZMod N,
    (rationalOutputDensity p Y N (Sum.elim aux b) : ℂ) *
      ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x
  have hunit : ∀ j, 1 / T j ≤ δ := by
    intro j
    apply le_trans _ (hmesh j)
    apply div_le_div_of_nonneg_right _ (hT j).le
    exact_mod_cast Nat.succ_le_of_lt (Nat.mul_pos (NeZero.pos qW) hcutoff)
  have hm := translatedGridMass_le g hg center T hT hR hδ hδ1 hunit hsupport
  have hd0 : 0 ≤ D / cutoff := div_nonneg hD (Nat.cast_nonneg _)
  have hraw0 := rationalOutputOrderTail_normalized_grid_le p Y N hD hP hdecay cutoff hcutoff
    g hg0 center T hT R hsupport (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun k => φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j))
    (fun k => hbound _ _)
  rw [rationalOutputOrderTail_grid_difference p Y N cutoff g center T hT R hsupport
    (fun k => Sum.elim aux (fun j => (k j : ZMod N)))
    (fun k => φ (fun j => (k j : ZMod qW)) (fun j => ((k j : ℝ) - center j) / T j))] at hraw0
  have hraw : ‖raw - rawRet‖ ≤ (D / cutoff) * ((∫ x, g x) +
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ) :=
    hraw0.trans (mul_le_mul_of_nonneg_left hm hd0)
  have href0 := rationalOutputOrderTail_mean_integral_le volume p Y N hD hP hdecay cutoff hcutoff
    g hg0 (compactBox_integrable g hg.continuous R hsupport) (fun b : J → ZMod N => Sum.elim aux b)
    (fun b x => φ (zmodPiReduction hW b) x) (fun b x => hbound _ _)
  have hdiff : (𝔼 b : J → ZMod N, rationalOutputOrderTail p Y N cutoff (Sum.elim aux b) *
      ∫ x, (g x : ℂ) * φ (zmodPiReduction hW b) x) = ref - refRet := by
    simp only [rationalOutputOrderTail, sub_mul, Finset.expect_sub_distrib, ref, refRet, trunc]
  rw [hdiff, norm_sub_rev] at href0
  have hret := retainedRationalOutput_grid_quadrature p Y qW hW aux cutoff
    g φ C L K hg hφ hcap hbound center T hT hR hδ hδ1 hmesh hsupport
  change ‖raw - ref‖ ≤ _
  have ht := (norm_sub_le_norm_sub_add_norm_sub raw rawRet ref).trans
    (add_le_add hraw ((norm_sub_le_norm_sub_add_norm_sub rawRet refRet ref).trans
      (add_le_add hret href0)))
  exact ht.trans_eq (by ring)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical NNReal
variable {Ω Aux J V : Type*} [Fintype Ω] [Fintype Aux] [Fintype J] [Fintype V]

theorem rationalOutput_partial_grid_comparison
    (p : FiniteProbabilityWeights Ω) (Y : Ω → (Aux ⊕ J) → ℤ)
    {N : ℕ} [NeZero N] (qW : ℕ) [NeZero qW] (hW : qW ∣ N)
    (aux : Aux → ZMod N) (cutoff : ℕ) (hcutoff : 0 < cutoff)
    {D P : ℝ} (hD : 0 ≤ D) (hP : ((Fintype.card (Aux ⊕ J) + 2 : ℕ) : ℝ) ≤ P)
    (hdecay : ∀ χ : AddChar ((Aux ⊕ J) → ZMod N) ℂ,
      ‖finiteImageCharacteristic p (fun x j => (Y x j : ZMod N)) χ‖ ≤
        D * (orderOf χ : ℝ) ^ (-P))
    (g : ((V → ℝ) × (J → ℝ)) → ℝ) (φ : (J → ZMod qW) → ((V → ℝ) × (J → ℝ)) → ℂ)
    (C L K : ℝ≥0) (hg : LipschitzWith L g) (hg0 : ∀ x, 0 ≤ g x)
    (hφ : ∀ b, LipschitzWith K (φ b))
    (hcap : ∀ x, |g x| ≤ C) (hbound : ∀ b x, ‖φ b x‖ ≤ 1)
    (center T : J → ℝ) (hT : ∀ j, 0 < T j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, ((qW * cutoff : ℕ) : ℝ) / T j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → g x = 0) :
    ‖∫ c : V → ℝ,
      ((∑' k : J → ℤ,
        (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
        (rationalOutputDensity p Y N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
        φ (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
        ((∏ j, T j : ℝ) : ℂ) -
      𝔼 b : J → ZMod N,
        (rationalOutputDensity p Y N (Sum.elim aux b) : ℂ) *
        ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x))‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) *
          (2 * R) ^ Fintype.card V +
        (2 * (D / cutoff)) * ∫ y, g y
          ∂((volume : Measure (V → ℝ)).prod (volume : Measure (J → ℝ))) := by
  classical
  let err := fun c : V → ℝ =>
    (∑' k : J → ℤ,
      (g (c, fun j => ((k j : ℝ) - center j) / T j) : ℂ) *
      (rationalOutputDensity p Y N (Sum.elim aux (fun j => (k j : ZMod N))) : ℂ) *
      φ (fun j => (k j : ZMod qW)) (c, fun j => ((k j : ℝ) - center j) / T j)) /
      ((∏ j, T j : ℝ) : ℂ) -
    𝔼 b : J → ZMod N, (rationalOutputDensity p Y N (Sum.elim aux b) : ℂ) *
      ∫ x, (g (c, x) : ℂ) * φ (zmodPiReduction hW b) (c, x)
  have herr0 (c : V → ℝ) (hc : R < ‖c‖) : err c = 0 := by
    have hz (x : J → ℝ) : g (c, x) = 0 := hsupport _ (hc.trans_le (norm_fst_le (c, x)))
    simp only [err, hz, Complex.ofReal_zero, zero_mul, integral_zero, mul_zero,
      Finset.expect_const_zero, tsum_zero, zero_div, sub_self]
  have herr (c : V → ℝ) (_hc : ‖c‖ ≤ R) : ‖err c‖ ≤
      ((cutoff : ℝ) ^ (Fintype.card (Aux ⊕ J) + 1) *
        (2 * (2 * R + 2) ^ Fintype.card J * ((L : ℝ) + C * K) * δ) +
        (D / cutoff) * ((2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ)) +
          (2 * (D / cutoff)) * ∫ x, g (c, x) := by
    have hg' : LipschitzWith L (fun x : J → ℝ => g (c, x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_prod_same_left] using hg.dist_le_mul (c, x) (c, y)
    have hφ' (b : J → ZMod qW) : LipschitzWith K (fun x : J → ℝ => φ b (c, x)) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simpa only [dist_prod_same_left] using (hφ b).dist_le_mul (c, x) (c, y)
    have he := rationalOutput_translated_grid_comparison p Y qW hW aux cutoff hcutoff hD hP hdecay
      (fun x => g (c, x)) (fun b x => φ b (c, x)) C L K hg' (fun x => hg0 _) hφ'
      (fun x => hcap _) (fun b x => hbound _ _) center T hT hR hδ hδ1 hmesh
      (fun x hx => hsupport _ (hx.trans_le (norm_snd_le (c, x))))
    exact he.trans_eq (by ring)
  exact compactSliceError_norm_integral_le g hg.continuous hg0 hR
    (mul_nonneg (by norm_num) (div_nonneg hD (Nat.cast_nonneg _))) hsupport err herr0 herr

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {n : Fin m → ℕ}
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "Active" => AllocatedActiveIntegerAxis U basis S.value
local notation "scale" => allocatedActiveIntegerGridScale U basis R S.value

theorem allocatedActiveInteger_periodic_quadrature
    (hR : ∀ j, 0 < R j) {H radius : ℝ} (hH : 0 ≤ H)
    (q : ℕ) [NeZero q] (hRinv : ∀ j, (R j)⁻¹ ≤ H) (hradius : 0 ≤ radius)
    (hmesh : (q : ℝ) * H / S.value ≤ 1)
    (f : (Active → ZMod q) → (Active → ℝ) → ℂ) {K : ℝ≥0}
    (hLip : ∀ r, LipschitzWith K (f r))
    (hsupport : ∀ r x, radius < ‖x‖ → f r x = 0) :
    ‖(∑' k : Active → ℤ,
        f (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
          ((∏ a, scale a : ℝ) : ℂ) - 𝔼 r : Active → ZMod q, ∫ x, f r x‖ ≤
      2 * (2 * radius + 2) ^ Fintype.card Active * (K : ℝ) *
        ((q : ℝ) * H / S.value) :=
  periodicIntegerGrid_complex_quadrature q f hLip scale
    (allocatedActiveIntegerGridScale_pos U basis hR S.value) hradius
    (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hH) (Nat.cast_nonneg _)) hmesh
    (fun a => allocatedActiveIntegerGridScale_mesh U basis hR S.positive
      (Nat.cast_nonneg _) hRinv a) hsupport

theorem allocatedActiveInteger_partial_periodic_quadrature
    {C : Type*} [Fintype C]
    (hR : ∀ j, 0 < R j) {H radius Rc : ℝ} (hH : 0 ≤ H)
    (q : ℕ) [NeZero q] (hRinv : ∀ j, (R j)⁻¹ ≤ H)
    (hradius : 0 ≤ radius) (hRc : 0 ≤ Rc) (hmesh : (q : ℝ) * H / S.value ≤ 1)
    (f : (C → ℝ) → (Active → ZMod q) → (Active → ℝ) → ℂ) {K : ℝ≥0}
    (hLip : ∀ v r, LipschitzWith K (f v r))
    (hsupport : ∀ v r x, radius < ‖x‖ → f v r x = 0)
    (hcontinuousSupport : ∀ v, Rc < ‖v‖ → ∀ r x, f v r x = 0) :
    ‖∫ v, ((∑' k : Active → ℤ,
        f v (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
          ((∏ a, scale a : ℝ) : ℂ) - 𝔼 r : Active → ZMod q, ∫ x, f v r x)‖ ≤
      (2 * (2 * radius + 2) ^ Fintype.card Active * (K : ℝ) *
        ((q : ℝ) * H / S.value)) * (2 * Rc) ^ Fintype.card C := by
  let err := fun v : C → ℝ => (∑' k : Active → ℤ,
      f v (fun a => (k a : ZMod q)) (fun a => (k a : ℝ) / scale a)) /
        ((∏ a, scale a : ℝ) : ℂ) - 𝔼 r : Active → ZMod q, ∫ x, f v r x
  have he (v : C → ℝ) : ‖err v‖ ≤
      2 * (2 * radius + 2) ^ Fintype.card Active * (K : ℝ) *
        ((q : ℝ) * H / S.value) :=
    allocatedActiveInteger_periodic_quadrature U basis B S hR hH q hRinv hradius hmesh
      (f v) (hLip v) (hsupport v)
  have hz (v : C → ℝ) (hv : Rc < ‖v‖) : ‖err v‖ = 0 := by
    simp only [err, hcontinuousSupport v hv, tsum_zero, zero_div, integral_zero,
      Finset.expect_const_zero, sub_self, norm_zero]
  have hb := integral_norm_le_box (fun v : C → ℝ => ‖err v‖) hRc hz
    (fun v _ => by simpa only [norm_norm] using he v)
  change ‖∫ v, err v‖ ≤ _
  exact (norm_integral_le_integral_norm err).trans (by simpa only [norm_norm] using hb)

end Erdos3.VectorPolynomial

end

end OAI
