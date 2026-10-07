import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer
import OAI.Combinatorics.Progressions.Sampling.ForecastGoodPathMeanNorm

namespace OAI

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem exists_measure_productive_good_path
    {H : Type*} [MeasurableSpace H] (μ : Measure H) [IsProbabilityMeasure μ]
    (productive : Set H) (hprod : MeasurableSet productive) (err : H → ℝ)
    (Q : H → Prop) (hQ : ∀ᵐ h ∂μ, Q h)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (herr : ∀ᵐ h ∂μ, 0 ≤ err h) (hi : Integrable err μ)
    (hmass : τ ≤ μ.real productive)
    (hmean : (∫ h, err h ∂μ) ≤ τ * r / 2) :
    ∃ h ∈ productive, Q h ∧ err h ≤ r := by
  classical
  by_contra! hn
  have hpoint : ∀ᵐ h ∂μ, productive.indicator (fun _ => r) h ≤ err h := by
    filter_upwards [hQ, herr] with h hq he
    by_cases hp : h ∈ productive
    · simpa only [Set.indicator_of_mem hp] using (hn h hp hq).le
    · simpa only [Set.indicator_of_notMem hp] using he
  have hh := integral_mono_ae ((integrable_const r).indicator hprod) hi hpoint
  rw [integral_indicator_const r hprod, smul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hmass hr.le
  nlinarith [mul_pos hτ hr]

theorem exists_measure_productive_averaged_model_transfer
    {H V I : Type*} [MeasurableSpace H]
    [AddCommGroup V] [Module ℂ V] [Fintype I]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (productive : Set H) (hprod : MeasurableSet productive)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e)
    (Q : H → Prop) (hQ : ∀ᵐ h ∂μ, Q h)
    {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (hmass : τ ≤ μ.real productive)
    (hi : Integrable (fun h =>
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖) μ)
    (hmean : (∫ h,
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖ ∂μ) ≤ τ * ρ / 4)
    (hscore : ∀ h ∈ productive, Q h → ρ ≤ (B h v).re) :
    ∃ h ∈ productive, Q h ∧ ρ / 2 ≤ (A h v).re := by
  let err := fun h =>
    (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖
  have herr : ∀ᵐ h ∂μ, 0 ≤ err h := Filter.Eventually.of_forall (by
    intro h
    dsimp only [err]
    positivity)
  obtain ⟨h, hp, hq, he⟩ := exists_measure_productive_good_path μ productive hprod
    err Q hQ hτ (show 0 < ρ / 2 by positivity) herr hi hmass
    (by convert hmean using 1; ring)
  refine ⟨h, hp, hq, ?_⟩
  have hd := (finite_model_test_difference_weighted (A h) (B h) v e J c hmodel).trans he
  have hre := (neg_le_abs ((A h v - B h v).re)).trans ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re] at hre
  linarith [hscore h hp hq]

theorem integral_weighted_model_error_le
    {H I : Type*} [MeasurableSpace H] [Fintype I]
    (μ : Measure H) (f : I → H → ℂ) (a b : H → ℂ) (c : I → ℂ)
    (hf : ∀ i, Integrable (f i) μ) (ha : Integrable a μ) (hb : Integrable b μ)
    {M η α β : ℝ} (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ i, (∫ h, ‖f i h‖ ∂μ) ≤ η)
    (hea : (∫ h, ‖a h‖ ∂μ) ≤ α) (heb : (∫ h, ‖b h‖ ∂μ) ≤ β) :
    Integrable (fun h => (∑ i, ‖c i‖ * ‖f i h‖) + ‖a h‖ + ‖b h‖) μ ∧
    (∫ h, (∑ i, ‖c i‖ * ‖f i h‖) + ‖a h‖ + ‖b h‖ ∂μ) ≤ M * η + α + β := by
  have hterm (i : I) : Integrable (fun h => ‖c i‖ * ‖f i h‖) μ :=
    (hf i).norm.const_mul _
  have hsum : Integrable (fun h => ∑ i, ‖c i‖ * ‖f i h‖) μ :=
    integrable_finsetSum _ (fun i _ => hterm i)
  refine ⟨(hsum.add ha.norm).add hb.norm, ?_⟩
  rw [integral_add (f := fun h => (∑ i, ‖c i‖ * ‖f i h‖) + ‖a h‖)
    (g := fun h => ‖b h‖) (hsum.add ha.norm) hb.norm,
    integral_add (f := fun h => ∑ i, ‖c i‖ * ‖f i h‖)
    (g := fun h => ‖a h‖) hsum ha.norm,
    integral_finsetSum _ (fun i _ => hterm i)]
  have hs : (∑ i, ∫ h, ‖c i‖ * ‖f i h‖ ∂μ) ≤ M * η := by
    calc
      _ = ∑ i, ‖c i‖ * (∫ h, ‖f i h‖ ∂μ) := by simp only [integral_const_mul]
      _ ≤ ∑ i, ‖c i‖ * η := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hatom i) (norm_nonneg _))
      _ = (∑ i, ‖c i‖) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ M * η := mul_le_mul_of_nonneg_right hc hη
  linarith

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem exists_measure_productive_path_off_exception
    {H : Type*} [MeasurableSpace H] (μ : Measure H) [IsProbabilityMeasure μ]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (err : H → ℝ) (Q : H → Prop) (hQ : ∀ᵐ h ∂μ, Q h)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r)
    (herr : ∀ᵐ h ∂μ, 0 ≤ err h) (hi : Integrable err μ)
    (hmass : τ ≤ μ.real productive) (hbadmass : μ.real bad ≤ τ / 4)
    (hmean : (∫ h, err h ∂μ) ≤ τ * r / 4) :
    ∃ h ∈ productive, h ∉ bad ∧ Q h ∧ err h ≤ r := by
  classical
  by_contra! hn
  have hpoint : ∀ᵐ h ∂μ, productive.indicator (fun _ => r) h ≤
      bad.indicator (fun _ => r) h + err h := by
    filter_upwards [hQ, herr] with h hq he
    by_cases hp : h ∈ productive
    · by_cases hb : h ∈ bad
      · simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hb]
        linarith
      · simp only [Set.indicator_of_mem hp, Set.indicator_of_notMem hb, zero_add]
        exact (hn h hp hb hq).le
    · simp only [Set.indicator_of_notMem hp]
      exact add_nonneg (Set.indicator_nonneg (fun _ _ => hr.le) _) he
  have hbi : Integrable (bad.indicator (fun _ : H => r)) μ :=
    (integrable_const r).indicator hbad
  have hh := integral_mono_ae ((integrable_const r).indicator hprod) (hbi.add hi) hpoint
  simp only [Pi.add_apply] at hh
  rw [integral_add hbi hi, integral_indicator_const r hprod,
    integral_indicator_const r hbad, smul_eq_mul, smul_eq_mul] at hh
  have hm := mul_le_mul_of_nonneg_right hmass hr.le
  have hb := mul_le_mul_of_nonneg_right hbadmass hr.le
  nlinarith [mul_pos hτ hr]

theorem exists_measure_model_transfer_off_exception
    {H V I : Type*} [MeasurableSpace H] [AddCommGroup V] [Module ℂ V] [Fintype I]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e)
    (err : H → ℝ) (Q : H → Prop) (hQ : ∀ᵐ h ∂μ, Q h)
    {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (herr : ∀ᵐ h ∂μ, 0 ≤ err h) (hi : Integrable err μ)
    (hmass : τ ≤ μ.real productive) (hbadmass : μ.real bad ≤ τ / 4)
    (hmean : (∫ h, err h ∂μ) ≤ τ * ρ / 8)
    (herror : ∀ h ∈ productive, h ∉ bad → Q h →
      (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) + ‖A h e‖ + ‖B h e‖ ≤ err h)
    (hscore : ∀ h ∈ productive, h ∉ bad → Q h → ρ ≤ (B h v).re) :
    ∃ h ∈ productive, h ∉ bad ∧ Q h ∧ ρ / 2 ≤ (A h v).re := by
  obtain ⟨h, hp, hb, hq, he⟩ := exists_measure_productive_path_off_exception
    μ productive bad hprod hbad err Q hQ hτ (show 0 < ρ / 2 by positivity)
    herr hi hmass hbadmass (by convert hmean using 1; ring)
  refine ⟨h, hp, hb, hq, ?_⟩
  have hd := (finite_model_test_difference_weighted (A h) (B h) v e J c hmodel).trans
    ((herror h hp hb hq).trans he)
  have hre := (neg_le_abs ((A h v - B h v).re)).trans ((Complex.abs_re_le_norm _).trans hd)
  simp only [Complex.sub_re] at hre
  linarith [hscore h hp hb hq]

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem exists_measure_averaged_buffered_score
    {H Ω U I : Type*} [MeasurableSpace H] [Fintype Ω] [Fintype U] [Fintype I] {m : ℕ}
    (law : Measure H) [IsProbabilityMeasure law]
    (productive : Set H) (hprod : MeasurableSet productive)
    (Qgood : H → Prop) (hQgood : ∀ᵐ h ∂law, Qgood h)
    (χ : PatchKernel m) (x : Ω → Fin m → ℝ)
    (T : Ω → (Fin m → ℤ) → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ)
    (f : Ω → ℝ) (lam : ℝ) (ψ : H → U → Ω)
    (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ x T f lam u : ℂ)) =
      (∑ i, c i • J i) + e) {τ ρ : ℝ}
    (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.real productive)
    (hi : Integrable (fun h =>
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * e u‖ +
      ‖𝔼 a, e (ψ h a)‖) law)
    (hmean : (∫ h,
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift (x u)) : ℂ) * e u‖ +
      ‖𝔼 a, e (ψ h a)‖ ∂law) ≤ τ * ρ / 4)
    (hscore : ∀ h ∈ productive, Qgood h → ρ ≤ 𝔼 a, bufferedScalarScore χ x T f lam (ψ h a)) :
    ∃ h ∈ productive, Qgood h ∧ ρ / 2 ≤ 𝔼 u, (f u - lam) * ∑' b,
      χ.value (fun i => x u i - (b i : ℝ)) * G h u b * T u b := by
  let A := fun h => finiteWeightedTest id (fun u => (G h u (nearestIntegerLift (x u)) : ℂ))
  let B := fun h => finiteWeightedTest (ψ h) (fun _ => (1 : ℂ))
  have hmean' : (∫ h, (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) +
      ‖A h e‖ + ‖B h e‖ ∂law) ≤ τ * ρ / 4 := by
    simpa only [A, B, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk, id_eq, one_mul] using hmean
  have hscore' : ∀ h ∈ productive, Qgood h → ρ ≤ (B h (fun u => (bufferedScalarScore χ x T f lam u : ℂ))).re := by
    intro h hh hq
    simpa only [B, ← Complex.ofReal_one, finiteWeightedTest_real, one_mul] using hscore h hh hq
  have hi' : Integrable (fun h => (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) +
      ‖A h e‖ + ‖B h e‖) law := by
    simpa only [A, B, finiteWeightedTest, LinearMap.coe_mk, AddHom.coe_mk, id_eq, one_mul] using hi
  obtain ⟨h, hh, hq, hs⟩ := exists_measure_productive_averaged_model_transfer law productive hprod A B
    _ e J c hmodel Qgood hQgood hτ hρ hmass hi' hmean' hscore'
  refine ⟨h, hh, hq, ?_⟩
  simpa only [A, finiteWeightedTest_real, id_eq, bufferedScalarScore_weighted] using hs

open MvPolynomial
open scoped NNReal

theorem exists_measure_averaged_modeled_discounted_patch
    {H σ Ω U I : Type*} [MeasurableSpace H] [Fintype Ω] [Fintype U] [Fintype I]
    {s d E m : ℕ} (law : Measure H) [IsProbabilityMeasure law]
    (productive : Set H) (hprod : MeasurableSet productive)
    (Qgood : H → Prop) (hQgood : ∀ᵐ h ∂law, Qgood h)
    (w : Fin d → ℕ) (hw : ∀ j, 1 ≤ w j) (hws : ∀ j, w j ≤ s) (hmono : Monotone w)
    (P : Fin d → MvPolynomial σ ℝ) (hP : ∀ j, P j ∈ weightedSupportLE (fun _ : σ => 1) (w j))
    (p : Fin m → ℕ) (B : WeightedParameterPatch (σ ⊕ Fin m) (Sum.elim (fun _ => 1) p) s E)
    (χ : PatchKernel m) (F : H → (Fin m → ℤ) → (Fin m → ℝ) → ℝ)
    (L C : ℝ≥0) (hC : 1 ≤ C)
    (hF : ∀ h ∈ productive, Qgood h → ∀ β, LipschitzWith L (F h β))
    (hFbound : ∀ h ∈ productive, Qgood h → ∀ β y, F h β y ∈ Set.Icc (0 : ℝ) C)
    (M : Fin m → Fin d → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (hweight : ∀ i j, M i j ≠ 0 → w j ≤ p i)
    (hinvariant : ∀ h ∈ productive, Qgood h → ∀ c k, F h (recoveredIntegerLift M c k) = F h c)
    (q : ℕ) (hq : 8 ≤ q) (hmesh : 16 * (K : ℝ) ≤ q)
    (t : Ω → σ → ℝ) (f : Ω → ℝ) (G : H → Ω → (Fin m → ℤ) → ℝ) {lam δ ε : ℝ}
    (hf : ∀ u, 0 ≤ f u) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ)
    (hdiscount : (1 + δ) * (1 - ε) ≤ 1 - δ)
    (hlower : ∀ h ∈ productive, Qgood h → ∀ u β, (1 - δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)) ≤ G h u β)
    (hupper : ∀ h ∈ productive, Qgood h → ∀ u β, G h u β ≤ (1 + δ) *
      F h β (fun i => realIntegerMatrix M (fun j => aeval (t u) (P j)) i - (β i : ℝ)))
    (ψ : H → U → Ω) (e : Ω → ℂ) (J : I → Ω → ℂ) (c : I → ℂ)
    (hmodel : (fun u => (bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam u : ℂ)) =
        (∑ i, c i • J i) + e)
    {τ ρ : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ) (hmass : τ ≤ law.real productive)
    (hi : Integrable (fun h =>
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ +
      ‖𝔼 a, e (ψ h a)‖) law)
    (hmean : (∫ h,
      (∑ i, ‖c i‖ * ‖(𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * J i u) -
        (𝔼 a, J i (ψ h a))‖) +
      ‖𝔼 u, (G h u (nearestIntegerLift
        (realIntegerMatrix M (fun j => aeval (t u) (P j)))) : ℂ) * e u‖ +
      ‖𝔼 a, e (ψ h a)‖ ∂law) ≤ τ * ρ / 4)
    (hscore : ∀ h ∈ productive, Qgood h → ρ ≤ 𝔼 a, bufferedScalarScore χ
      (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
      (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) f lam (ψ h a)) :
    ∃ Q : PolynomialPatch σ s (d + E),
      Q.kernel.lip ≤ (q : ℝ≥0) * (2 * (q : ℝ≥0) ^ d + 1) +
        (χ.lip + L / C) * K + B.kernel.lip ∧
      (ρ / 2) / ((1 + δ) * (C : ℝ) * (q : ℝ) ^ d) ≤
        𝔼 u, (f u - (1 - ε) * lam) * Q.value (t u) := by
  obtain ⟨h, hh, hqgood, hs⟩ := exists_measure_averaged_buffered_score law productive hprod Qgood hQgood χ
    (fun u => realIntegerMatrix M (fun j => aeval (t u) (P j)))
    (fun u b => B.value (Sum.elim (t u) (fun i => (b i : ℝ)))) G
    f lam ψ e J c hmodel hτ hρ hmass hi hmean hscore
  exact exists_discounted_recovered_patch w hw hws hmono P hP p B χ (F h) L C hC
    (hF h hh hqgood) (hFbound h hh hqgood) M K hM hweight (hinvariant h hh hqgood) q hq hmesh
    t f (G h) hf hlam hδ hdiscount (hlower h hh hqgood) (hupper h hh hqgood) hs

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators

theorem exists_measure_model_transfer_of_good_atom_bounds
    {H V I : Type*} [MeasurableSpace H] [AddCommGroup V] [Module ℂ V] [Fintype I]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e)
    (Q : H → Prop) (hQ : ∀ᵐ h ∂μ, Q h)
    {τ ρ M η α β : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (hη : 0 ≤ η) (hβ : 0 ≤ β) (hc : (∑ i, ‖c i‖) ≤ M)
    (hmass : τ ≤ μ.real productive) (hbadmass : μ.real bad ≤ τ / 4)
    (hatomMeas : ∀ i, AEStronglyMeasurable (fun h => A h (J i) - B h (J i)) μ)
    (hatom : ∀ i, ∀ᵐ h ∂μ, h ∉ bad → ‖A h (J i) - B h (J i)‖ ≤ η)
    (ha : Integrable (fun h => A h e) μ)
    (hlocal : (∫ h, ‖A h e‖ ∂μ) ≤ α)
    (hb : AEStronglyMeasurable (fun h => B h e) μ)
    (hforecast : ∀ᵐ h ∂μ, h ∉ bad → ‖B h e‖ ≤ β)
    (hbudget : M * η + α + β ≤ τ * ρ / 8)
    (hscore : ∀ h ∈ productive, h ∉ bad → Q h → ρ ≤ (B h v).re) :
    ∃ h ∈ productive, h ∉ bad ∧ Q h ∧ ρ / 2 ≤ (A h v).re := by
  classical
  let f : I → H → ℂ := fun i => badᶜ.indicator (fun h => A h (J i) - B h (J i))
  let b : H → ℂ := badᶜ.indicator (fun h => B h e)
  have hf (i : I) : Integrable (f i) μ ∧ (∫ h, ‖f i h‖ ∂μ) ≤ η :=
    integral_norm_off_exception_le μ _ bad hbad hη (hatomMeas i) (hatom i)
  have hb' : Integrable b μ ∧ (∫ h, ‖b h‖ ∂μ) ≤ β :=
    integral_norm_off_exception_le μ _ bad hbad hβ hb hforecast
  obtain ⟨hi, hmean⟩ := integral_weighted_model_error_le μ f (fun h => A h e) b c
    (fun i => (hf i).1) ha hb'.1 hη hc (fun i => (hf i).2) hlocal hb'.2
  apply exists_measure_model_transfer_off_exception μ productive bad hprod hbad A B v e J c
    hmodel (fun h => (∑ i, ‖c i‖ * ‖f i h‖) + ‖A h e‖ + ‖b h‖) Q hQ
    hτ hρ (Filter.Eventually.of_forall (fun h => by positivity)) hi hmass hbadmass
    (hmean.trans hbudget) _ hscore
  intro h _ hg _
  have hc' : h ∈ badᶜ := hg
  simp only [f, b, Set.indicator_of_mem hc', le_refl]

theorem exists_measure_model_transfer_of_uniform_good_comparison
    {H V I : Type*} [MeasurableSpace H] [AddCommGroup V] [Module ℂ V] [Fintype I]
    (μ : Measure H) [IsProbabilityMeasure μ]
    (productive bad : Set H) (hprod : MeasurableSet productive) (hbad : MeasurableSet bad)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ)
    (hmodel : v = (∑ i, c i • J i) + e)
    (Q : H → Prop) (hQ : ∀ᵐ h ∂μ, Q h)
    {τ ρ M η : ℝ} (hτ : 0 < τ) (hρ : 0 < ρ)
    (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hmass : τ ≤ μ.real productive) (hbadmass : μ.real bad ≤ τ / 4)
    (hatom : ∀ h ∈ productive, h ∉ bad → Q h →
      ∀ i, ‖A h (J i) - B h (J i)‖ ≤ η)
    (hb : Integrable (fun h => B h e) μ)
    (hlocal : (∫ h, ‖B h e‖ ∂μ) ≤ τ * ρ / 32)
    (hforecast : ∀ h ∈ productive, h ∉ bad → Q h → ‖A h e‖ ≤ ρ / 8)
    (hbudget : M * η ≤ ρ / 8)
    (hscore : ∀ h ∈ productive, h ∉ bad → Q h → ρ ≤ (B h v).re) :
    ∃ h ∈ productive, h ∉ bad ∧ Q h ∧ ρ / 2 ≤ (A h v).re := by
  obtain ⟨h, hp, hb, hq, he⟩ := exists_measure_productive_path_off_exception
    μ productive bad hprod hbad (fun h => ‖B h e‖) Q hQ hτ
    (show 0 < ρ / 8 by positivity)
    (Filter.Eventually.of_forall (fun h => norm_nonneg _)) hb.norm hmass hbadmass
    (by convert hlocal using 1; ring)
  refine ⟨h, hp, hb, hq, ?_⟩
  have hatomSum : (∑ i, ‖c i‖ * ‖A h (J i) - B h (J i)‖) ≤ ρ / 8 := by
    calc
      _ ≤ ∑ i, ‖c i‖ * η := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hatom h hp hb hq i) (norm_nonneg _))
      _ = (∑ i, ‖c i‖) * η := (Finset.sum_mul _ _ _).symm
      _ ≤ M * η := mul_le_mul_of_nonneg_right hc hη
      _ ≤ ρ / 8 := hbudget
  have hd := finite_model_test_difference_weighted (A h) (B h) v e J c hmodel
  have hre := (neg_le_abs ((A h v - B h v).re)).trans (Complex.abs_re_le_norm _)
  simp only [Complex.sub_re] at hre
  linarith [hforecast h hp hb hq, hscore h hp hb hq]

end Erdos3

end

end OAI
