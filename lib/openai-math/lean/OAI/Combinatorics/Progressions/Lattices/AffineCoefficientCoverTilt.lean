import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import OAI.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
import OAI.Combinatorics.Progressions.Lattices.SmoothResidueWindowMass
import OAI.Combinatorics.Progressions.Probability.DensityIntegralBound
import OAI.Combinatorics.Progressions.Probability.ProbabilityIntegralApproximation

namespace OAI

section

namespace Erdos3

open Polynomial

theorem exists_integer_cover_threshold (A₀ : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      Real.exp ((P + A₀) ^ A₀) ≤ Real.exp ((P + A) ^ A) ∧
      Real.exp P * Real.exp ((P + A₀) ^ A₀) ≤ Real.exp ((P + A) ^ A) := by
  obtain ⟨A, hA, hpoly⟩ := exists_natPolynomial_eval_budget (X + (X + C A₀) ^ A₀ + 1)
  refine ⟨A, hA, ?_⟩
  intro P hP
  have he : P + (P + A₀) ^ A₀ + 1 ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hpoly P hP
  constructor
  · apply Real.exp_le_exp.mpr
    linarith
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

theorem affineSampleCoefficientArray_smul {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (r : ℝ) (b : Option K → I → ℝ) :
    affineSampleCoefficientArray U (fun j => r • p j)
      (fun j => coefficients_smul_mem (U j) (p j) (hm j) r) b =
      r • affineSampleCoefficientArray U p hm b := by
  funext s
  apply Subtype.ext
  change (affineSampleCoefficientArray U (fun j => r • p j) _ b s).val =
    r • (affineSampleCoefficientArray U p hm b s).val
  rw [affineSampleCoefficientArray_val, affineSampleCoefficientArray_val]
  simp only [map_smul, Finsupp.smul_apply]

noncomputable def affineCoefficientCoverSample {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (b : Option K → I → ℝ) : CoefficientTorus (K := K) U :=
  QuotientAddGroup.mk' (coefficientIntegerLattice U) ((q : ℝ)⁻¹ • affineSampleCoefficientArray U p hm b)

theorem affineCoefficientCoverSample_eq_scaled {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (b : Option K → I → ℝ) :
    affineCoefficientCoverSample U p hm q b =
      affineSampleCoefficientTorus U (fun j => (q : ℝ)⁻¹ • p j)
        (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹) b := by
  rw [affineSampleCoefficientTorus, affineSampleCoefficientArray_smul]
  rfl

theorem affineCoefficientCoverSample_projection {I K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ))
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (hq : 0 < q) (b : Option K → I → ℝ) :
    quotientIntegerCover (coefficientIntegerLattice U) q (affineCoefficientCoverSample U p hm q b) =
      affineSampleCoefficientTorus U p hm b := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [affineCoefficientCoverSample, quotientIntegerCover_mk,
    smul_smul, mul_inv_cancel₀ hq0, one_smul]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_haar_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        coefficientTorusFourierSum U frequency c
          (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, coefficientTorusFourierSum U frequency c x ∂μ)‖ ≤ ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_affine_coefficient_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  obtain ⟨hZ, hnorm⟩ := hnormalization hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [coefficientTorusFourierSum_integral]
  simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using hnorm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  obtain ⟨hZ, hcomp⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  let g := coefficientTorusFourierSum U frequency c
  let sample (z : Option K × I → ℤ) := affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))
  let E (a : CoefficientTorus (K := K) U → ℂ) :=
    ∑' z, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) * a (sample z)
  have hfirst := selectedResidueSmoothPMF_approximation stride G V hV hZ
    (fun _ => 1) (fun z => f (sample z)) (fun z => g (sample z)) hη
    (fun _ _ => by simp) (fun z _ => happrox (sample z))
  simp only [one_mul] at hfirst
  have hlast := probability_integral_approximation μ g f
    (coefficientTorusFourierSum_integrable U frequency c μ) hf
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E g) (∫ x, f x ∂μ)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E g) (∫ x, g x ∂μ) (∫ x, f x ∂μ)
  change ‖E f - E g‖ ≤ η at hfirst
  change ‖E g - ∫ x, g x ∂μ‖ ≤ ε at hcomp
  change ‖E f - ∫ x, f x ∂μ‖ ≤ 2 * η + ε
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A₀, _, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  obtain ⟨A, hA, hbudget⟩ := exists_integer_cover_threshold A₀
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm q hq hqP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  have hb := hbudget P hP
  have hR0 : 0 ≤ R := (Real.exp_pos _).le.trans hR
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hscaledR : Real.exp ((P + A₀) ^ A₀) ≤ R / q := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hqP (Real.exp_pos ((P + A₀) ^ A₀)).le
      _ ≤ Real.exp ((P + A) ^ A) := hb.2
      _ ≤ R := hR
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    (fun j => (q : ℝ)⁻¹ • p j) (fun j => (hp j).smul (q : ℝ)⁻¹)
    (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹)
    stride hs hS hSP hρ hε hρP hεP hstride H (fun k => hb.1.trans (hsize k))
    (fun j => (hrank j).div_nat hR0 q hq) hscaledR G hG V hV hwidth f hf hη happrox
  refine ⟨hZ, ?_⟩
  simpa only [affineCoefficientCoverSample_eq_scaled] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_density_mass (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ _hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    |selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) - 1| ≤
      2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth D hD hDmass η hη happrox
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    (fun x => (D x : ℂ)) hD.ofReal hη happrox
  refine ⟨hZ, ?_⟩
  rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he
  rw [← selectedResidueDensityMass_complex stride G V hV hZ
    (fun z => D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))),
    ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he
  exact he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_tilted_family_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (F : Bool → Type*) [∀ b, Fintype (F b)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : ∀ b, F b → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ b a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency b a j d t : ℝ)| ≤ C)
    (c : ∀ b, F b → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : ∀ b, (∑ a, ‖c b a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (cover : ℕ) (_hcover : 0 < cover) (_hcoverP : (cover : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) (_hD0 : ∀ x, 0 ≤ D x)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : AEStronglyMeasurable f μ)
    (_hfbound : ∀ x, ‖f x‖ ≤ 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ b x,
      ‖(D x : ℂ) * (if b then f x else 1) - coefficientTorusFourierSum U (frequency b) (c b) x‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    (1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ))))) ∧
    (selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) ≤ 3 / 2) ∧
    ‖(∑' z, ((selectedResidueDensityPMF stride G V hV hZ
        (fun z => D (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ))))
        (fun _z => _hD0 _) hDpos z).toReal : ℂ) *
          f (affineCoefficientCoverSample U p _hm cover (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, (D x : ℂ) * f x ∂μ)‖ ≤ 4 * (2 * η + ε) := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm cover hcover hcoverP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound η hη happrox hsmall
  let sample (z : Option K × I → ℤ) := affineCoefficientCoverSample U p hm cover (fun k j => (z (k, j) : ℝ))
  obtain ⟨hZ, he0⟩ := hcomparison hP hn hd U μ hC hCP (frequency false) (hbound false)
    (c false) hB hBP (hcoefficients false) p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ)) hD.ofReal hη
    (fun x => by simpa using happrox false x)
  have hmass : |selectedResidueDensityMass stride G V (fun z => D (sample z)) - 1| ≤ 2 * η + ε := by
    rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he0
    rw [← selectedResidueDensityMass_complex stride G V hV hZ (fun z => D (sample z)),
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he0
    exact he0
  have hlower : 1 / 2 ≤ selectedResidueDensityMass stride G V (fun z => D (sample z)) := by
    have := (abs_le.mp hmass).1
    linarith
  have hupper : selectedResidueDensityMass stride G V (fun z => D (sample z)) ≤ 3 / 2 := by
    have := (abs_le.mp hmass).2
    linarith
  have hDpos : 0 < selectedResidueDensityMass stride G V (fun z => D (sample z)) := by linarith
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  obtain ⟨hZ', he1⟩ := hcomparison hP hn hd U μ hC hCP (frequency true) (hbound true)
    (c true) hB hBP (hcoefficients true) p hp hm cover hcover hcoverP stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ) * f x)
    (density_mul_integrable μ D hD f hf hfbound) hη
    (fun x => by simpa using happrox true x)
  have he := selectedResidueDensityPMF_error stride G V hV hZ
    (fun z => D (sample z)) (fun z => hD0 _) hDpos (fun z => f (sample z))
    hlower he1 hmass (norm_density_integral_le_one μ D hD hD0 hDmass f hfbound)
  convert he using 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_tilted_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : Bool → F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ b a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency b a j d t : ℝ)| ≤ C)
    (c : Bool → F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : ∀ b, (∑ a, ‖c b a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) (_hD0 : ∀ x, 0 ≤ D x)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : AEStronglyMeasurable f μ)
    (_hfbound : ∀ x, ‖f x‖ ≤ 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ b x,
      ‖(D x : ℂ) * (if b then f x else 1) - coefficientTorusFourierSum U (frequency b) (c b) x‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    (1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))))) ∧
    (selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) ≤ 3 / 2) ∧
    ‖(∑' z, ((selectedResidueDensityPMF stride G V hV hZ
        (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))))
        (fun _z => _hD0 _) hDpos z).toReal : ℂ) *
          f (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, (D x : ℂ) * f x ∂μ)‖ ≤ 4 * (2 * η + ε) := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_haar_approximation m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound η hη happrox hsmall
  let sample (z : Option K × I → ℤ) := affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))
  obtain ⟨hZ, he0⟩ := hcomparison hP hn hd U μ hC hCP (frequency false) (hbound false)
    (c false) hB hBP (hcoefficients false) p hp hm stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ)) hD.ofReal hη
    (fun x => by simpa using happrox false x)
  have hmass : |selectedResidueDensityMass stride G V (fun z => D (sample z)) - 1| ≤ 2 * η + ε := by
    rw [integral_complex_ofReal, hDmass, Complex.ofReal_one] at he0
    rw [← selectedResidueDensityMass_complex stride G V hV hZ (fun z => D (sample z)),
      ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he0
    exact he0
  have hlower : 1 / 2 ≤ selectedResidueDensityMass stride G V (fun z => D (sample z)) := by
    have := (abs_le.mp hmass).1
    linarith
  have hupper : selectedResidueDensityMass stride G V (fun z => D (sample z)) ≤ 3 / 2 := by
    have := (abs_le.mp hmass).2
    linarith
  have hDpos : 0 < selectedResidueDensityMass stride G V (fun z => D (sample z)) := by linarith
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  obtain ⟨hZ', he1⟩ := hcomparison hP hn hd U μ hC hCP (frequency true) (hbound true)
    (c true) hB hBP (hcoefficients true) p hp hm stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR G hG V hV hwidth (fun x => (D x : ℂ) * f x)
    (density_mul_integrable μ D hD f hf hfbound) hη
    (fun x => by simpa using happrox true x)
  have he := selectedResidueDensityPMF_error stride G V hV hZ
    (fun z => D (sample z)) (fun z => hD0 _) hDpos (fun z => f (sample z))
    hlower he1 hmass (norm_density_integral_le_one μ D hD hD0 hDmass f hfbound)
  convert he using 1; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_coefficient_cover_tilted_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : Bool → F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ b a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency b a j d t : ℝ)| ≤ C)
    (c : Bool → F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : ∀ b, (∑ a, ‖c b a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) (_hD0 : ∀ x, 0 ≤ D x)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : AEStronglyMeasurable f μ)
    (_hfbound : ∀ x, ‖f x‖ ≤ 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ b x,
      ‖(D x : ℂ) * (if b then f x else 1) - coefficientTorusFourierSum U (frequency b) (c b) x‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    (1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ))))) ∧
    (selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))) ≤ 3 / 2) ∧
    ‖(∑' z, ((selectedResidueDensityPMF stride G V hV hZ
        (fun z => D (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ))))
        (fun _z => _hD0 _) hDpos z).toReal : ℂ) *
          f (affineCoefficientCoverSample U p _hm q (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, (D x : ℂ) * f x ∂μ)‖ ≤ 4 * (2 * η + ε) := by
  obtain ⟨A₀, _, hcomparison⟩ := exists_affine_coefficient_tilted_comparison m
  obtain ⟨A, hA, hbudget⟩ := exists_integer_cover_threshold A₀
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm q hq hqP stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound η hη happrox hsmall
  have hb := hbudget P hP
  have hR0 : 0 ≤ R := (Real.exp_pos _).le.trans hR
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hscaledR : Real.exp ((P + A₀) ^ A₀) ≤ R / q := by
    apply (le_div_iff₀ hq0).mpr
    calc
      _ ≤ Real.exp P * Real.exp ((P + A₀) ^ A₀) := by
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right hqP (Real.exp_pos ((P + A₀) ^ A₀)).le
      _ ≤ Real.exp ((P + A) ^ A) := hb.2
      _ ≤ R := hR
  have he := hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    (fun j => (q : ℝ)⁻¹ • p j) (fun j => (hp j).smul (q : ℝ)⁻¹)
    (fun j => coefficients_smul_mem (U j) (p j) (hm j) (q : ℝ)⁻¹)
    stride hs hS hSP hρ hε hρP hεP hstride H (fun k => hb.1.trans (hsize k))
    (fun j => (hrank j).div_nat hR0 q hq) hscaledR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound hη happrox hsmall
  simpa only [affineCoefficientCoverSample_eq_scaled] using he

end Erdos3.VectorPolynomial

end

end OAI
