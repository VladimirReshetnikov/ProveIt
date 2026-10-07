import OAI.Combinatorics.Progressions.Estimates.PhysicalRowsSiteReconstruction
import OAI.Combinatorics.Progressions.Lattices.IntegerPeriodPivot

namespace OAI


namespace Erdos3

theorem linearIndependent_of_fixed_kernel_period {O K₀ K : Type*}
    [Fintype O] [DecidableEq O] [Fintype K₀]
    (A₀ : Matrix O K₀ ℤ) (A : Matrix O K ℤ) (e : K₀ → K)
    (he : ∀ i k, A i (e k) = A₀ i k) {a : ℤ} (ha : a ≠ 0)
    (hperiod : integerScalarLattice O a ≤ A₀.mulVecLin.range) :
    LinearIndependent ℝ (fun i k => (A i k : ℝ)) := by
  classical
  obtain ⟨s, hs⟩ := integerPeriod_exists_pivot A₀ ha hperiod
  have hdet : ((A₀.submatrix id s).map (fun z => (z : ℝ))).det ≠ 0 := by
    rw [← Int.cast_det]
    exact_mod_cast hs
  let restrict : (K → ℝ) →ₗ[ℝ] (O → ℝ) :=
    { toFun := fun v j => v (e (s j))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  change LinearIndependent ℝ (fun i j => (A₀ i (s j) : ℝ)) at hrows
  apply LinearIndependent.of_comp restrict
  simpa only [Function.comp_def, restrict, LinearMap.coe_mk, AddHom.coe_mk,
    he] using hrows

end Erdos3


namespace Erdos3.BooleanCubeKernel

open VectorPolynomial Polynomial
open scoped BigOperators

theorem exists_fixed_kernel_covered_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK₀ : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite₀ : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C),
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
    ∀ (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
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
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          retainedSiteFourierSum U root difference frequency b c
            (affineCoveredSiteSample U root difference D p hm (fun k j => (z (k, j) : ℝ)))))‖ ≤ ε := by
  obtain ⟨A₀, _, hprojection⟩ := exists_affine_cube_fourier_projection m q
  obtain ⟨A₁, _, hcover⟩ := exists_fixed_kernel_site_fourier_projection m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A₀) ^ A₀ + (X + Polynomial.C A₁) ^ A₁)
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK₀ hsite₀
  have hsum : (P + A₀) ^ A₀ + (P + A₁) ^ A₁ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hb₀ : (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₁)) A₁]
  have hb₁ : (P + A₁) ^ A₁ ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₀)) A₀]
  obtain ⟨D, hD, hDP, hrows⟩ := hcover root₀ difference₀ a ha hperiod hP hK₀ hsite₀
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hb₁), ?_⟩
  intro I K _ _ _ J _ F _ hn hd U root difference e hroot hdifference L C hL hC hLP hCP
    hsite frequency hbound
  have hlin := linearIndependent_of_fixed_kernel_period
    (Matrix.of difference₀) (Matrix.of difference) e hdifference ha hperiod
  obtain ⟨b, hb, heq⟩ := hrows root difference e hroot hdifference U frequency
    (fun a j d hd t => (hbound a j d hd t).trans hCP)
  refine ⟨b, fun a j s t => (hb a j s t).trans (Real.exp_le_exp.mpr hb₁), ?_⟩
  intro c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  obtain ⟨hZ, hproj⟩ := hprojection hP hn hd U root difference hlin hL hC hLP hCP hsite
    frequency hbound c hB hBP hcoefficients p hp hm stride hs hS hSP hρ hε hρP hεP
    hstride H (fun k => (Real.exp_le_exp.mpr hb₀).trans (hsize k)) hrank
    ((Real.exp_le_exp.mpr hb₀).trans hR) Q hQ test htest G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  have hfun : affineCubeFourierProjection U root difference frequency p c =
      fun x => retainedSiteFourierSum U root difference frequency b c
        (affineCoveredSiteSample U root difference D p hm x) := funext (fun x => heq p hp hm c x)
  rw [hfun] at hproj
  exact hproj

end Erdos3.BooleanCubeKernel


namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem selectedResidue_density_projection_error
    {I K F : Type*} [Fintype I] [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (D : ℕ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (htest : ∀ s x, ‖test s x‖ ≤ 1)
    (base : I → ℤ) (modulus : I → ℕ)
    (T : Finset (ColumnResiduePattern (Option K) I modulus))
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T V z)
    (density : (Option K × I → ℤ) → ℝ)
    {η δ : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ z ∈ rectangularWeightIndices 0 V 1,
      ‖(density z : ℂ) - affineCubeFourierSum frequency
        (fun j => VectorPolynomial.translate (fun i => (base i : ℝ)) (p j)) c (fun k i => (z (k, i) : ℝ))‖ ≤ η)
    (hprojection :
      ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight 0 (fun s => affineSite root difference s)
          (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
          affineCubeFourierSum frequency (fun j => VectorPolynomial.translate (fun i => (base i : ℝ)) (p j)) c
            (fun k i => (z (k, i) : ℝ)))) -
        (∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
          (layeredSiteWeight 0 (fun s => affineSite root difference s)
            (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
            retainedSiteFourierSum U root difference frequency b c
              (affineCoveredSiteSample U root difference D
                (fun j => VectorPolynomial.translate (fun i => (base i : ℝ)) (p j))
                (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
                (fun k i => (z (k, i) : ℝ)))))‖ ≤ δ)
    : ‖(∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight 0 (fun s => affineSite root difference s)
          (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ)) *
          (density z : ℂ))) -
      ∑' z, ((selectedResidueSmoothPMF modulus T V hV hZ z).toReal : ℂ) *
        physicalCubeCoveredTest U root difference D p hm frequency b c test
          (physicalCubeRootDifferences root (Matrix.of difference) base z)‖ ≤ η + δ := by
  let law := selectedResidueSmoothPMF modulus T V hV hZ
  let w := fun z : Option K × I → ℤ => layeredSiteWeight 0 (fun s => affineSite root difference s)
    (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun k i => (z (k, i) : ℝ))
  let fourier := fun z : Option K × I → ℤ => affineCubeFourierSum frequency
    (fun j => VectorPolynomial.translate (fun i => (base i : ℝ)) (p j)) c (fun k i => (z (k, i) : ℝ))
  let φ := physicalCubeCoveredTest U root difference D p hm frequency b c test
  let output := physicalCubeRootDifferences root (Matrix.of difference) base
  let projected := fun z : Option K × I → ℤ => w z *
    retainedSiteFourierSum U root difference frequency b c
      (affineCoveredSiteSample U root difference D
        (fun j => VectorPolynomial.translate (fun i => (base i : ℝ)) (p j))
        (fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j))
        (fun k i => (z (k, i) : ℝ)))
  have hfactor : projected = fun z => φ (output z) := by
    funext z
    exact physicalCubeCoveredTest_of_frame U root difference D p hm frequency b c test base z
  have hfirst : ‖(∑' z, ((law z).toReal : ℂ) * (w z * (density z : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * (w z * fourier z)‖ ≤ η :=
    selectedResidueSmoothPMF_approximation modulus T V hV hZ w (fun z => (density z : ℂ)) fourier hη
      (fun z _ => layeredSiteWeight_norm_le 0 _ _ (fun s x => htest s _) _) happrox
  have hp := hprojection
  change ‖(∑' z, ((law z).toReal : ℂ) * (w z * fourier z)) -
    ∑' z, ((law z).toReal : ℂ) * projected z‖ ≤ δ at hp
  rw [hfactor] at hp
  have hprojected : ‖(∑' z, ((law z).toReal : ℂ) * (w z * (density z : ℂ))) -
      ∑' z, ((law z).toReal : ℂ) * φ (output z)‖ ≤ η + δ :=
    (norm_sub_le_norm_sub_add_norm_sub _
      (∑' z, ((law z).toReal : ℂ) * (w z * fourier z)) _).trans (add_le_add hfirst hp)
  exact hprojected

end Erdos3.BooleanCubeKernel


namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_fixed_kernel_density_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK₀ : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite₀ : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    (_hn : (Fintype.card I : ℝ) ≤ P) (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (e : K₀ → K) (_hroot : ∀ k, root (e k) = root₀ k)
    (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C),
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
    ∀ (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ δ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hδ : 0 < δ)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hδP : 1 / δ ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ s x, ‖test s x‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option K) I stride)) (_hT : T.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (density : CoefficientTorus (K := K) U → ℝ) {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(density x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z,
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root (Matrix.of difference) base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ))) : ℂ))) -
        ∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          physicalCubeCoveredTest U root difference D p hm frequency b c test
            (physicalCubeRootDifferences root (Matrix.of difference) base z)‖ ≤ η + δ := by
  obtain ⟨A, hA, hprojection⟩ := exists_fixed_kernel_covered_projection m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK₀ hsite₀
  obtain ⟨D, hD, hDP, hrows⟩ := hprojection root₀ difference₀ a ha hperiod hP hK₀ hsite₀
  refine ⟨D, hD, hDP, ?_⟩
  intro I K _ _ _ J _ F _ hn hd U root difference e hroot hdifference L C hL hC hLP hCP
    hsite frequency hbound
  obtain ⟨b, hb, hproj⟩ := hrows hn hd U root difference e hroot hdifference hL hC hLP hCP hsite
    frequency hbound
  refine ⟨b, hb, ?_⟩
  intro c B hB hBP hcoefficients p hp hm base stride hs R S ρ δ hS hSP hρ hδ hρP hδP
    hstride H hsize hrank hR test htest T hT V hV hwidth density η hη happrox
  let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
  let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
  have hpa (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hra (j) : HasLayerSamplingRank (j.val + 1) H R (U j) (pa j) :=
    (hasLayerSamplingRank_translate_iff (fun i => (base i : ℝ)) (j.val + 1) H R (U j) (p j) (hp j)).mpr (hrank j)
  obtain ⟨hZ, hproj⟩ := hproj c hB hBP hcoefficients pa hpa hma stride hs
    hS hSP hρ hδ hρP hδP hstride H hsize hra hR 0 (by simp)
    (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun s x => htest s _) T hT V hV hwidth
  refine ⟨hZ, ?_⟩
  have happ (z : Option K × I → ℤ) :
      ‖(density (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ))) : ℂ) -
        affineCubeFourierSum frequency pa c (fun k i => (z (k, i) : ℝ))‖ ≤ η := by
    simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ pa hpa hma,
      affineCubeFourierSum] using happrox (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ)))
  simpa only [layeredSiteWeight_physicalCube] using
    selectedResidue_density_projection_error U root difference D p hm frequency b c test htest base
      stride T V hV hZ (fun z => density (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ))))
      hη (fun z _ => happ z) hproj

end Erdos3.BooleanCubeKernel

end OAI
