import OAI.Combinatorics.Progressions.Estimates.OneSiteWeightIdentity
import OAI.Combinatorics.Progressions.Fourier.CoefficientFourierTranslation
import OAI.Combinatorics.Progressions.Linear.ProductOneSiteProjectionCap

namespace OAI

section

namespace Erdos3

theorem selectedResidueDensityPMF_test_le {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D g φ : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    {C ε a : ℝ} (ha : 0 < a) (hlower : a ≤ selectedResidueDensityMass modulus G V D)
    (hg : ∀ x, g x ≤ C) (hφ : ∀ x, 0 ≤ φ x)
    (he : |(∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (D x * φ x)) -
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (g x * φ x)| ≤ ε) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * φ x) ≤
      (C * (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * φ x) + ε) / a := by
  let prob := selectedResidueFiniteLaw modulus G V hV hZ
  have hmean (f : (K × I → ℤ) → ℝ) : prob.mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x :=
    selectedResidueFiniteLaw_mean modulus G V hV hZ f
  have hm : prob.mean (fun x => D x.val) = selectedResidueDensityMass modulus G V D :=
    selectedResidueFiniteLaw_densityMass modulus G V hV hZ D
  have hb := prob.mean_mul_le_of_capped_comparison (ε := ε) (fun x => D x.val) (fun x => g x.val)
    (fun x => φ x.val) (fun x => hφ x.val) (fun x => hg x.val)
    (by
      rw [hmean (fun x => D x * φ x), hmean (fun x => g x * φ x)]
      exact he)
  have hn := prob.reweightPositive_test_le (fun x => D x.val) (fun x => hD0 x.val)
    (hm.symm ▸ hD) (fun x => φ x.val) (fun x => hφ x.val) ha (hm.symm ▸ hlower) hb
  rw [FiniteProbabilityWeights.reweightPositive_mean, hm,
    hmean (fun x => D x * φ x), hmean φ] at hn
  rw [selectedResidueDensityPMF_mean]
  exact hn

theorem selectedResidueDensityPMF_test_le_of_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D g φ : (K × I → ℤ) → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < selectedResidueDensityMass modulus G V D)
    {C ε a : ℝ} (ha : 0 < a) (hlower : a ≤ selectedResidueDensityMass modulus G V D)
    (hg : ∀ x, g x ≤ C) (hφ : ∀ x, 0 ≤ φ x)
    (he : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((φ x : ℂ) * (D x : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) * ((φ x : ℂ) * (g x : ℂ))‖ ≤ ε) :
    (∑' x, (selectedResidueDensityPMF modulus G V hV hZ D hD0 hD x).toReal * φ x) ≤
      (C * (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * φ x) + ε) / a := by
  apply selectedResidueDensityPMF_test_le modulus G V hV hZ D g φ hD0 hD ha hlower hg hφ
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he
  simpa only [mul_comm, mul_left_comm, mul_assoc] using he

end Erdos3

end

section

namespace Erdos3

theorem selectedResidueSmoothPMF_test_le_of_complex {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) (G : Finset (ColumnResiduePattern K I modulus))
    (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight modulus G V x)
    (D g φ : (K × I → ℤ) → ℝ) {C ε : ℝ}
    (hg : ∀ x, g x ≤ C) (hφ : ∀ x, 0 ≤ φ x)
    (he : ‖(∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        ((φ x : ℂ) * (D x : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF modulus G V hV hZ x).toReal : ℂ) *
        ((φ x : ℂ) * (g x : ℂ))‖ ≤ ε) :
    (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * (φ x * D x)) ≤
      C * (∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * φ x) + ε := by
  let prob := selectedResidueFiniteLaw modulus G V hV hZ
  have hmean (f : (K × I → ℤ) → ℝ) : prob.mean (fun x => f x.val) =
      ∑' x, (selectedResidueSmoothPMF modulus G V hV hZ x).toReal * f x :=
    selectedResidueFiniteLaw_mean modulus G V hV hZ f
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_tsum, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at he
  have h := prob.mean_mul_le_of_capped_comparison (ε := ε) (fun x => D x.val)
    (fun x => g x.val) (fun x => φ x.val) (fun x => hφ x.val) (fun x => hg x.val) (by
      rw [hmean (fun x => D x * φ x), hmean (fun x => g x * φ x)]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using he)
  rw [hmean (fun x => D x * φ x), hmean φ] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial

noncomputable def physicalAffineSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (z : Option K × I → ℤ) : I → ℝ :=
  integerSiteValue (fun k => match k with | none => 1 | some k => root k)
    (fun k j => (z (k,j) : ℝ))

theorem integerSiteValue_oneSite {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (z : Option K × I → ℤ) :
    integerSiteValue (affineSite root difference ∅) (fun k j => (z (k,j) : ℝ)) =
      physicalAffineSite root z := by
  have hs : affineSite root difference ∅ = (fun k => match k with | none => 1 | some k => root k) := by
    funext k
    cases k <;> simp [affineSite]
  rw [hs]
  rfl

theorem layeredSiteWeight_physical {I K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ) (φ : (I → ℝ) → ℂ)
    (z : Option K × I → ℤ) :
    layeredSiteWeight 0 (fun s => affineSite root difference s) (fun _ => φ)
      (fun k j => (z (k,j) : ℝ)) = φ (physicalAffineSite root z) := by
  rw [layeredSiteWeight_oneSite, integerSiteValue_oneSite]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem selectedResidue_oneSite_density_error {I K F : Type*} [Fintype I] [Fintype K] [Fintype F]
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U t y x)) μ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (G : Finset (ColumnResiduePattern (Option K) I stride))
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x)
    (w : (Option K × I → ℤ) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hprojection : ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * affineCubeFourierSum frequency p c (fun k j => (x (k, j) : ℝ)))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * affineCubeFourierProjection U t difference frequency p c (fun k j => (x (k, j) : ℝ)))‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * (D (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ))) : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
          (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ)))) : ℝ) : ℂ))‖ ≤ 2 * η + ε := by
  let prob := selectedResidueFiniteLaw stride G V hV hZ
  have hmean (f : (Option K × I → ℤ) → ℂ) : prob.complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) * f x :=
    selectedResidueFiniteLaw_complexMean stride G V hV hZ f
  have hw' : prob.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (prob.mean_mono (fun x => hw x.val)).trans_eq (prob.mean_const 1)
  have he := oneSiteDensity_projection_error (ε := ε) U t difference frequency c μ D hη happrox p hp hm
    prob (fun x k j => (x.val (k, j) : ℝ)) (fun x => w x.val) (fun _ _ => hD _) hw'
    (by
      rw [hmean (fun x => w x * affineCubeFourierSum frequency p c (fun k j => (x (k, j) : ℝ))),
        hmean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (fun k j => (x (k, j) : ℝ)))]
      exact hprojection)
  rw [hmean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ))) : ℂ)),
    hmean (fun x => w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
      (affineSampleCoefficientTorus U p hm (fun k j => (x (k, j) : ℝ)))) : ℝ) : ℂ))] at he
  simpa only [mul_one] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_affine_oneSite_density_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin 0)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
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
    (test : Finset (Fin 0) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          (D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          ((coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root
            (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) : ℝ) : ℂ)))‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hprojection⟩ := exists_affine_cube_fourier_projection m 0
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ root difference
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest
    G hG V hV hwidth D hD η hη happrox
  obtain ⟨hZ, he⟩ := hprojection hP hn hd U root difference linearIndependent_empty_type
    hL hC hLP hCP hsite frequency hbound c hB hBP hcoefficients p hp hm stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  exact selectedResidue_oneSite_density_error U root difference frequency c μ D hη happrox hD p hp hm
    stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    (fun z => layeredSiteWeight_norm_le Q _ test htest _) he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_affine_oneSite_test_domination (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin 0)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
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
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (_hD0 : ∀ x, 0 ≤ D x) {M a : ℝ} (_ha : 0 < a)
    (_hlower : a ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))))
    (_hcap : ∀ y, coefficientFiberAverage U μ root D y ≤ M)
    (φ : (I → ℝ) → ℝ) (_hφ : ∀ v, φ v ∈ Set.Icc (0 : ℝ) 1),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))),
    (∑' z, (selectedResidueDensityPMF stride G V hV hZ
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))))
      (fun _ => _hD0 _) hDpos z).toReal *
        φ (integerSiteValue (affineSite root difference ∅) (fun k j => (z (k, j) : ℝ)))) ≤
      (M * (∑' z, (selectedResidueSmoothPMF stride G V hV hZ z).toReal *
        φ (integerSiteValue (affineSite root difference ∅) (fun k j => (z (k, j) : ℝ)))) +
        (2 * η + ε)) / a := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_oneSite_density_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ root difference
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    G hG V hV hwidth D hD η hη happrox hD0 M a ha hlower hcap φ hφ
  have hφn (v : I → ℝ) : ‖(φ v : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ v).1]
    exact (hφ v).2
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ root difference hL hC hLP hCP hsite frequency hbound
    c hB hBP hcoefficients p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    0 (by simp) (fun _ v => (φ v : ℂ)) (fun _ v => hφn v) G hG V hV hwidth D hD hη happrox
  have hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))) := ha.trans_le hlower
  refine ⟨hZ, hDpos, ?_⟩
  simp only [layeredSiteWeight_oneSite] at he
  exact selectedResidueDensityPMF_test_le_of_complex (C := M) (ε := 2 * η + ε) (a := a) stride G V hV hZ
    (fun z => D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ))))
    (fun z => coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root
      (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))))
    (fun z => φ (integerSiteValue (affineSite root difference ∅) (fun k j => (z (k, j) : ℝ))))
    (fun _ => hD0 _) hDpos ha hlower
    (fun _ => hcap _) (fun _ => (hφ _).1) he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_affine_translated_oneSite_density_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ k, |(root k : ℝ)| ≤ L)
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
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Measurable D)
    {M : ℝ} (_hDbound : ∀ x, ‖D x‖ ≤ M)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(D x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η)
    (center : CoefficientTorus (K := K) U)
    (φphysical : (I → ℝ) → ℂ) (_hφ : ∀ v, ‖φphysical v‖ ≤ 1),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (φphysical (physicalAffineSite root z) *
          (D (center + affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))) : ℂ))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (φphysical (physicalAffineSite root z) *
          (((coefficientFiberAverage U μ root (fun x => D (center + x))
            (coefficientEvaluationTorus U root
              (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))))) : ℝ) : ℂ)))‖ ≤
      2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_oneSite_density_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ root
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    G hG V hV hwidth D hD M hDbound η hη happrox center φphysical hφ
  let difference : Fin 0 → K → ℤ := fun i => Fin.elim0 i
  have hsite' (s : Finset (Fin 0)) (k : K) :
      |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L := by
    have hs : s = ∅ := Subsingleton.elim _ _
    simpa [hs, affineSite] using hsite k
  have hcoefficients' :
      (∑ a, ‖c a * coefficientTorusCharacter U (frequency a) center‖) ≤ B := by
    rw [coefficientFourier_translate_norm]
    exact hcoefficients
  have happrox' (x) :
      ‖coefficientTorusFourierSum U frequency
        (fun a => c a * coefficientTorusCharacter U (frequency a) center) x -
        (D (center + x) : ℂ)‖ ≤ η := by
    rw [norm_sub_rev]
    exact coefficientFourier_translate_approx U D frequency c happrox center x
  have hintegrable (y) :
      Integrable (fun x => D (center + coefficientFiberMap U root y x)) μ :=
    bounded_coefficient_translate_fiber_integrable U μ D hD hDbound center root y
  obtain ⟨hZ, he⟩ := hcomparison hP hn hd U μ root difference hL hC hLP hCP hsite'
    frequency hbound (fun a => c a * coefficientTorusCharacter U (frequency a) center)
    hB hBP hcoefficients' p hp hm stride hs hS hSP hρ hε hρP hεP hstride
    H hsize hrank hR 0 (by simp) (fun _ => φphysical) (fun _ => hφ)
    G hG V hV hwidth (fun x => D (center + x)) hintegrable hη happrox'
  refine ⟨hZ, ?_⟩
  simpa only [layeredSiteWeight_physical] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_affine_oneSite_normalized_domination (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin 0)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
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
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hDglobal : Integrable D μ) (_hDmass : (∫ x, D x ∂μ) = 1)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2)
    (_hD0 : ∀ x, 0 ≤ D x) {M : ℝ}
    (_hcap : ∀ y, coefficientFiberAverage U μ root D y ≤ M)
    (φ : (I → ℝ) → ℝ) (_hφ : ∀ v, φ v ∈ Set.Icc (0 : ℝ) 1),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ)))) ∧
    (∑' z, (selectedResidueDensityPMF stride G V hV hZ
      (fun z => D (affineSampleCoefficientTorus U p _hm (fun k j => (z (k, j) : ℝ))))
      (fun _ => _hD0 _) hDpos z).toReal *
        φ (integerSiteValue (affineSite root difference ∅) (fun k j => (z (k, j) : ℝ)))) ≤
      (M * (∑' z, (selectedResidueSmoothPMF stride G V hV hZ z).toReal *
        φ (integerSiteValue (affineSite root difference ∅) (fun k j => (z (k, j) : ℝ)))) +
        (2 * η + ε)) / (1 / 2 : ℝ) := by
  obtain ⟨A₀, hA₀, hmass⟩ := exists_affine_coefficient_density_mass m
  obtain ⟨A₁, _hA₁, hdom⟩ := exists_affine_oneSite_test_domination m
  let A := max A₀ A₁
  have hA : 2 ≤ A := hA₀.trans (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U _ _ μ _ _ root difference
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR
    G hG V hV hwidth D hDglobal hDmass hD η hη happrox hsmall hD0 M hcap φ hφ
  have hthreshold (a : ℕ) (ha : a ≤ A) : Real.exp ((P + a) ^ a) ≤ Real.exp ((P + A) ^ A) := by
    apply Real.exp_le_exp.mpr
    have haa : (a : ℝ) ≤ A := by exact_mod_cast ha
    have hbase : P + (a : ℝ) ≤ P + A := by linarith
    have hAreal : (2 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by positivity) hbase a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P + A) ha)
  have h₀ := hthreshold A₀ (le_max_left _ _)
  have h₁ := hthreshold A₁ (le_max_right _ _)
  obtain ⟨_hZ₀, he⟩ := hmass hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients p hp hm
    stride hs hS hSP hρ hε hρP hεP hstride H (fun k => h₀.trans (hsize k)) hrank (h₀.trans hR)
    G hG V hV hwidth D hDglobal hDmass hη (fun x => by rw [norm_sub_rev]; exact happrox x)
  have hlower : 1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineSampleCoefficientTorus U p hm (fun k j => (z (k, j) : ℝ)))) := by
    have hh := (abs_le.mp he).1
    linarith
  obtain ⟨hZ, hDpos, hb⟩ := hdom hP hn hd U μ root difference hL hC hLP hCP hsite frequency hbound
    c hB hBP hcoefficients p hp hm stride hs hS hSP hρ hε hρP hεP hstride
    H (fun k => h₁.trans (hsize k)) hrank (h₁.trans hR) G hG V hV hwidth D hD hη happrox
    hD0 (by norm_num : (0 : ℝ) < 1 / 2) hlower hcap φ hφ
  exact ⟨hZ, hDpos, he, hlower, hb⟩

end Erdos3.BooleanCubeKernel

end

end OAI
