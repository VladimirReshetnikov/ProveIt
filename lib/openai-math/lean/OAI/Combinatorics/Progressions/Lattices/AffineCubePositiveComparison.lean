import OAI.Combinatorics.Progressions.Fourier.SectionRetainedFourier
import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_approximated_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
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
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f g : (Option K × I → ℤ) → ℂ) {η : ℝ} (_hη : 0 ≤ η)
    (_hf : ∀ z ∈ rectangularWeightIndices 0 V 1,
      ‖f z - affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ))‖ ≤ η)
    (_hg : ∀ z ∈ rectangularWeightIndices 0 V 1,
      ‖affineCubeFourierProjection U root difference frequency p c (fun k j => (z (k, j) : ℝ)) - g z‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) * f z)) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) * g z))‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hprojection⟩ := exists_affine_cube_fourier_projection m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth f g η hη hf hg
  obtain ⟨hZ, hproj⟩ := hprojection hP hn hd U root difference hlin hL hC hLP hCP hsite
    frequency hbound c hB hBP hcoefficients p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  exact selectedResidueSmoothPMF_projection_approximation stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    f (fun z => affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ)))
    (fun z => affineCubeFourierProjection U root difference frequency p c (fun k j => (z (k, j) : ℝ)))
    g hη (fun z _ => layeredSiteWeight_norm_le Q _ test htest _) hf hg hproj

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped Classical

theorem affineCubeModeFactors_iff_bounded {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) :
    affineCubeModeFactors U root difference frequency ↔
      ∀ j, ∃ M : (Finset (Fin q) → U j) →ₗ[ℝ] ℝ,
        ∀ p : VectorPolynomial K ℝ (U j), DegreeLE (1 : K → ℕ) (j.val + 1) p →
          coefficientFunctional (fun d a => (frequency j d a : ℝ)) (map (U j).subtype p) =
            M (VectorPolynomial.siteEvaluation (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) p) := by
  constructor
  · exact affineCubeModeFactors_bounded U root difference frequency
  · intro h j
    obtain ⟨M, hM⟩ := h j
    refine ⟨M, ?_⟩
    let L := (coefficientFunctional (fun d a => (frequency j d a : ℝ))).comp (map (U j).subtype)
    have hh := (homogeneous_site_factorization_iff (j.val + 1)
      (fun s k => ((affineSite root difference s (some k) : ℤ) : ℝ)) L M).mpr hM
    change ∀ p, Homogeneous (j.val + 1) p → affineModeLift L p = _ at hh
    have he : (fun s (k : Option K) => k.elim (1 : ℝ)
        (fun k => ((affineSite root difference s (some k) : ℤ) : ℝ))) =
        (fun s => affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) := by
      funext s k
      cases k <;> simp [affineSite, Int.cast_sum]
    simpa only [L, affineModeLift_comp_map, LinearMap.comp_apply, he] using hh

theorem exists_affine_cube_residual {K : Type*} [Fintype K] (m q : ℕ)
    (root : K → ℤ) (difference : Fin q → K → ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hsite : ∀ (s : Finset (Fin q)) k, (affineSite root difference s (some k)).natAbs ≤ H) :
    ∃ (d : Fin m → ℕ)
      (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ),
      (∀ j, 0 < d j) ∧
      ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)),
        let R := coefficientSiteResidual U (fun s k => affineSite root difference s (some k)) d T
        (∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U) ∧
        ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
          (coefficientArrayFunctional U frequency).comp R = 0 ↔
            affineCubeModeFactors U root difference frequency := by
  let site := fun s k => affineSite root difference s (some k)
  have hex (j : Fin m) := exists_integer_site_residual (boundedSiteMatrix (j.val + 1) site)
    (Nat.one_le_pow _ _ hH) (boundedSiteMatrix_height (j.val + 1) site hH hsite)
  choose d T hd hT _hbound using hex
  refine ⟨d, T, hd, ?_⟩
  intro J _ U
  refine ⟨coefficientSiteResidual_preserves_lattice U site d T, ?_⟩
  intro frequency
  rw [coefficientSiteResidual_zero_iff U site d T hd (fun j x => hT j x),
    affineCubeModeFactors_iff_bounded]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

variable {K : Type*} [Fintype K] {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
  (U : ∀ j, Submodule ℝ (J j → ℝ))
  (R : CoefficientArray (K := K) U →ₗ[ℝ] CoefficientArray (K := K) U)
  (hR : ∀ x ∈ coefficientIntegerLattice U, R x ∈ coefficientIntegerLattice U)
  [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

theorem coefficientResidual_section_integrable
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (f : CoefficientTorus (K := K) U → W) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) (x : CoefficientTorus (K := K) U) :
    Integrable (fun y => f (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ := by
  have hc := linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hR
    R.continuous_of_finiteDimensional
  exact Integrable.of_bound (hf.comp (continuous_const.add hc)).aestronglyMeasurable B
    (ae_of_all μ (fun _ => hB _))

theorem coefficientResidualAverage_continuous
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (μ : Measure (CoefficientTorus (K := K) U)) [IsFiniteMeasure μ]
    (f : CoefficientTorus (K := K) U → W) (hf : Continuous f)
    {B : ℝ} (hB : ∀ x, ‖f x‖ ≤ B) :
    Continuous (linearQuotientAverage (coefficientIntegerLattice U) R hR μ f) := by
  apply continuous_of_dominated
    (fun x => (coefficientResidual_section_integrable U R hR μ f hf hB x).aestronglyMeasurable)
    (fun _ => ae_of_all μ (fun _ => hB _)) (integrable_const B)
  exact ae_of_all μ (fun _ => hf.comp (continuous_id.add continuous_const))

theorem coefficientTorusFourierSum_residualAverage {F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (x : CoefficientTorus (K := K) U) :
    linearQuotientAverage (coefficientIntegerLattice U) R hR μ (coefficientTorusFourierSum U frequency c) x =
      ∑ a, if affineCubeModeFactors U root difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0 := by
  have hi (a : F) := coefficientResidual_section_integrable U R hR μ
    (coefficientTorusCharacter U (frequency a))
    (quotientLinearCharacter_continuous _ _ _ (coefficientArrayFunctional U (frequency a)).continuous_of_finiteDimensional)
    (fun x => (quotientLinearCharacter_norm _ _ _ x).le) x
  change (∫ y, ∑ a, c a * coefficientTorusCharacter U (frequency a)
    (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y) ∂μ) = _
  rw [integral_finsetSum _ (fun a _ => (hi a).const_mul (c a))]
  simp only [integral_const_mul]
  change (∑ a, c a * linearQuotientAverage (coefficientIntegerLattice U) R hR μ
    (quotientLinearCharacter (coefficientIntegerLattice U) (coefficientArrayFunctional U (frequency a))
      (coefficientArrayFunctional_integral U (frequency a))) x) = _
  simp only [linearQuotientAverage_character, hfactor, mul_ite, mul_zero]
  rfl

theorem affineCubeFourierProjection_eq_residualAverage {I F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (b : Option K → I → ℝ) :
    affineCubeFourierProjection U root difference frequency p c b =
      linearQuotientAverage (coefficientIntegerLattice U) R hR μ (coefficientTorusFourierSum U frequency c)
        (affineSampleCoefficientTorus U p hm b) := by
  rw [coefficientTorusFourierSum_residualAverage U R hR root difference hfactor]
  simp only [coefficientTorusCharacter_sample U _ p hp hm b, affineCubeFourierProjection]

theorem coefficientTorusFourierProjection_approx_residualAverage {F : Type*} [Fintype F]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    (hfactor : ∀ frequency : ∀ j, (K →₀ ℕ) → J j → ℤ,
      (coefficientArrayFunctional U frequency).comp R = 0 ↔ affineCubeModeFactors U root difference frequency)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η : ℝ}
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (x : CoefficientTorus (K := K) U)
    (hD : Integrable (fun y => D (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ) :
    ‖(∑ a, if affineCubeModeFactors U root difference (frequency a) then
        c a * coefficientTorusCharacter U (frequency a) x else 0) -
      ((linearQuotientAverage (coefficientIntegerLattice U) R hR μ D x : ℝ) : ℂ)‖ ≤ η := by
  rw [← coefficientTorusFourierSum_residualAverage U R hR root difference hfactor frequency c μ x]
  have hi : Integrable (fun y => coefficientTorusFourierSum U frequency c
      (x + linearQuotientEndomorphism (coefficientIntegerLattice U) R hR y)) μ := by
    apply integrable_finsetSum
    intro a _
    apply Integrable.const_mul
    exact coefficientResidual_section_integrable U R hR μ (coefficientTorusCharacter U (frequency a))
      (quotientLinearCharacter_continuous _ _ _ (coefficientArrayFunctional U (frequency a)).continuous_of_finiteDimensional)
      (fun x => (quotientLinearCharacter_norm _ _ _ x).le) x
  have he := linearQuotientAverage_approx (coefficientIntegerLattice U) R hR μ
    (coefficientTorusFourierSum U frequency c) (fun x => (D x : ℂ)) happrox x hi hD.ofReal
  simpa only [linearQuotientAverage, integral_complex_ofReal] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_affine_cube_positive_density {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hsite : ∀ (s : Finset (Fin q)) k, (affineSite root difference s (some k)).natAbs ≤ H)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (hD : Continuous D) {B : ℝ}
    (hcap : ∀ x, D x ∈ Set.Icc (0 : ℝ) B) (hmass : (∫ x, D x ∂μ) = 1) :
    ∃ g : CoefficientTorus (K := K) U → ℝ,
      Continuous g ∧ (∀ x, g x ∈ Set.Icc (0 : ℝ) B) ∧ Integrable g μ ∧ (∫ x, g x ∂μ) = 1 ∧
      ∀ {F : Type*} [Fintype F] (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
        {η : ℝ}, (∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η) →
        ∀ x, ‖(∑ a, if affineCubeModeFactors U root difference (frequency a) then
          c a * coefficientTorusCharacter U (frequency a) x else 0) - (g x : ℂ)‖ ≤ η := by
  obtain ⟨d, T, _, hR⟩ := exists_affine_cube_residual m q root difference hH hsite
  obtain ⟨hlattice, hfactor⟩ := hR U
  let R := coefficientSiteResidual U (fun s k => affineSite root difference s (some k)) d T
  let g := linearQuotientAverage (coefficientIntegerLattice U) R hlattice μ D
  have hRm := (linearQuotientEndomorphism_continuous (coefficientIntegerLattice U) R hlattice
    R.continuous_of_finiteDimensional).measurable
  have hb (x) : ‖D x‖ ≤ B := by rw [Real.norm_of_nonneg (hcap x).1]; exact (hcap x).2
  have hi : Integrable D μ := Integrable.of_bound hD.aestronglyMeasurable B (ae_of_all μ hb)
  have hp := linearQuotientAverage_probability (coefficientIntegerLattice U) R hlattice μ hRm D
    hD.measurable hi (fun x => (hcap x).1) hmass
  refine ⟨g, ?_, ?_, hp.2.1, hp.2.2, ?_⟩
  · exact coefficientResidualAverage_continuous U R hlattice μ D hD hb
  · intro x
    refine ⟨hp.1 x, ?_⟩
    have h := linearQuotientAverage_bound (coefficientIntegerLattice U) R hlattice μ D hb x
    rwa [Real.norm_of_nonneg (hp.1 x)] at h
  · intro F _ frequency c η happrox x
    exact coefficientTorusFourierProjection_approx_residualAverage U R hlattice root difference hfactor
      frequency c μ D happrox x (coefficientResidual_section_integrable U R hlattice μ D hD hb x)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators Classical

theorem exists_affine_cube_positive_comparison (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Continuous D) {B₀ η : ℝ}
    (_hcap : ∀ x, D x ∈ Set.Icc (0 : ℝ) B₀) (_hmass : (∫ x, D x ∂μ) = 1) (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η),
    ∃ g : CoefficientTorus (K := K) U → ℝ,
      Continuous g ∧ (∀ x, g x ∈ Set.Icc (0 : ℝ) B₀) ∧ Integrable g μ ∧ (∫ x, g x ∂μ) = 1 ∧
      ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
        ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
            (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
              (D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
          (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
            (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
              (g (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))) : ℂ)))‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hprojection⟩ := exists_affine_cube_approximated_projection m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U root difference hlin L C hL hC hLP hCP hsite
    frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth _ _ μ _ _ D hD B₀ η hcap hmass hη happrox
  let H₀ := max 1 (Finset.univ.sup (fun sk : Finset (Fin q) × K =>
    (affineSite root difference sk.1 (some sk.2)).natAbs))
  have hH₀ : 1 ≤ H₀ := le_max_left _ _
  have hsite₀ (s : Finset (Fin q)) (k : K) : (affineSite root difference s (some k)).natAbs ≤ H₀ :=
    (Finset.le_sup (f := fun sk : Finset (Fin q) × K =>
      (affineSite root difference sk.1 (some sk.2)).natAbs) (Finset.mem_univ (s, k))).trans (le_max_right _ _)
  obtain ⟨g, hgm, hgc, hgi, hgmass, hg⟩ :=
    exists_affine_cube_positive_density U root difference hH₀ hsite₀ μ D hD hcap hmass
  refine ⟨g, hgm, hgc, hgi, hgmass, ?_⟩
  apply hprojection hP hn hd U root difference hlin hL hC hLP hCP hsite frequency hbound c
    hB hBP hcoefficients p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    Q hQ test htest G hG V hV hwidth
    (fun z => (D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))) : ℂ))
    (fun z => (g (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))) : ℂ)) hη
  · intro z _
    have h := happrox (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))
    simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm,
      affineCubeFourierSum, norm_sub_rev] using h
  · intro z _
    have h := hg frequency c happrox (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))
    simpa only [coefficientTorusCharacter_sample U _ p hp hm, affineCubeFourierProjection] using h

end Erdos3.BooleanCubeKernel

end

end OAI
