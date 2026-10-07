/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AnchoredCubeCongruenceRemoval
import OAI.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
import OAI.Combinatorics.Progressions.Fourier.SectionPolynomialCharacter
import OAI.Combinatorics.Progressions.Lattices.AffineCoveredSiteValues
import OAI.Combinatorics.Progressions.Linear.FixedKernelGeometricCover

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

noncomputable def affineCubeFourierSum {I K F : Type*} [Fintype K] [Fintype F] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (c : F → ℂ) (b : Option K → I → ℝ) : ℂ :=
  ∑ a, c a * layeredCoefficientCharacter
    (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b

noncomputable def affineCubeFourierProjection {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)) (c : F → ℂ) (b : Option K → I → ℝ) : ℂ :=
  ∑ a, if affineCubeModeFactors U root difference (frequency a) then
    c a * layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ)))) p b else 0

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_affine_cube_fourier_projection (m q : ℕ) :
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
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierSum frequency p c (fun k j => (z (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)) *
          affineCubeFourierProjection U root difference frequency p c (fun k j => (z (k, j) : ℝ))))‖ ≤ ε := by
  obtain ⟨A₀, _, hremove⟩ := exists_affine_cube_congruence_removal m q
  obtain ⟨A₁, _, hthreshold⟩ := exists_cube_residue_threshold_exp_budget m q
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  classical
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C L S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    hL (hLP.trans hEP) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m (cubeModePolynomialBudget_pos q hL).le
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  apply le_trans ?_ (fourierModeError_cost_le hB hε)
  unfold affineCubeFourierSum affineCubeFourierProjection
  apply selectedResidueSmoothPMF_discard_error stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => (z (k, j) : ℝ)))
    c (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => (z (k, j) : ℝ)))
    (fun a => affineCubeModeFactors U root difference (frequency a)) hcoefficients hδ.le
  intro a hbad
  obtain ⟨_, hr⟩ := hremove (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
    U root difference hlin hL hC (hLP.trans hEP) (hCP.trans hEP) hsite (frequency a) (hbound a)
    ((not_affineCubeModeFactors_iff U root difference (frequency a)).mp hbad)
    p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
    H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) Q hQ test htest G hG V hV hwidth
  simpa only [layeredModeTestedPhase_eq_weight_mul] using hr

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators

theorem exists_anchored_affine_cube_fourier_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    (anchor : Option K × I → ℤ)
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
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => ((anchor + z) (k, j) : ℝ)) *
          affineCubeFourierSum frequency p c (fun k j => ((anchor + z) (k, j) : ℝ)))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => ((anchor + z) (k, j) : ℝ)) *
          affineCubeFourierProjection U root difference frequency p c (fun k j => ((anchor + z) (k, j) : ℝ))))‖ ≤ ε := by
  obtain ⟨A₀, _, hremove⟩ := exists_anchored_affine_cube_congruence_removal m q
  obtain ⟨A₁, _, hthreshold⟩ := exists_cube_residue_threshold_exp_budget m q
  obtain ⟨A, hA, hbudget⟩ := exists_fourier_uniform_budget A₀ A₁
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ anchor J _ F _ P hP hn hd U root difference hlin L C hL hC hLP hCP
    hsite frequency hbound c B hB hBP hcoefficients p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP
    hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  classical
  let P' := 2 * P + 2
  let δ := fourierModeError B ε
  have hPP : P ≤ P' := by dsimp [P']; linarith
  have hEP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP
  have hδ : 0 < δ := fourierModeError_pos hB hε
  have hδP : 1 / δ ≤ Real.exp P' := fourierModeError_inv_le_exp hP hB hBP hε hεP
  obtain ⟨hb₀, hb₁⟩ := hbudget P hP
  obtain ⟨hside, _⟩ := hthreshold (Fintype.card I) (Fintype.card (Option K × I))
    P' C L S ρ δ (hP.trans hPP) (hn.trans hPP) (hd.trans hPP) hC (hCP.trans hEP)
    hL (hLP.trans hEP) hS (hSP.trans hEP) hρ (hρP.trans hEP) hδ hδP
  have hZ := selectedResidueSmoothWeight_pos_of_threshold m (cubeModePolynomialBudget_pos q hL).le
    hS hρ hδ stride hs hstride H (fun j => hside.trans (hb₁.trans (hsize j))) G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  apply le_trans ?_ (fourierModeError_cost_le hB hε)
  unfold affineCubeFourierSum affineCubeFourierProjection
  apply selectedResidueSmoothPMF_discard_error stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => ((anchor + z) (k, j) : ℝ)))
    c (fun a z => layeredCoefficientCharacter
      (fun j => affineModeLift (coefficientFunctional (fun d t => (frequency a j d t : ℝ))))
      p (fun k j => ((anchor + z) (k, j) : ℝ)))
    (fun a => affineCubeModeFactors U root difference (frequency a)) hcoefficients hδ.le
  intro a hbad
  obtain ⟨_, hr⟩ := hremove anchor (hP.trans hPP) (hn.trans hPP) (hd.trans hPP)
    U root difference hlin hL hC (hLP.trans hEP) (hCP.trans hEP) hsite (frequency a) (hbound a)
    ((not_affineCubeModeFactors_iff U root difference (frequency a)).mp hbad)
    p hp hm stride hs hS (hSP.trans hEP) hρ hδ (hρP.trans hEP) hδP hstride
    H (fun j => hb₀.trans (hsize j)) hrank (hb₀.trans hR) Q hQ test htest G hG V hV hwidth
  simpa only [layeredModeTestedPhase_eq_weight_mul] using hr

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

noncomputable def retainedSiteFourierSum {K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (x : ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j)) : ℂ :=
  ∑ a, if affineCubeModeFactors U root difference (frequency a) then
    c a * ∏ j, subspaceArrayCharacter (U j) (b a j) (x j) else 0

theorem retainedSiteFourierSum_norm_le {K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ) (c : F → ℂ)
    (x : ∀ j, SubspaceArrayTorus (Finset (Fin q)) (U j)) :
    ‖retainedSiteFourierSum U root difference frequency b c x‖ ≤ ∑ a, ‖c a‖ := by
  unfold retainedSiteFourierSum
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : affineCubeModeFactors U root difference (frequency a)
  · simp [ha, norm_prod, subspaceArrayCharacter_norm]
  · simp [ha]

theorem exists_geometric_site_fourier_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K : Type*} [Fintype K]
    (root : K → ℤ) (difference : Fin q → K → ℤ)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t,
      |(frequency a j d t : ℝ)| ≤ Real.exp P),
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ {I : Type*} (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
        (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : F → ℂ) (x : Option K → I → ℝ),
        affineCubeFourierProjection U root difference frequency p c x =
          retainedSiteFourierSum U root difference frequency b c
            (affineCoveredSiteSample U root difference D p hm x) := by
  obtain ⟨A, hA, hcover⟩ := exists_geometric_retained_common_cover m q
  refine ⟨A, hA, ?_⟩
  intro K _ root difference P hP hK hsite
  obtain ⟨D, hD, hDP, hrows⟩ := hcover root difference hP hK hsite
  refine ⟨D, hD, hDP, ?_⟩
  intro J _ F _ U frequency hfrequency
  choose b hb hchar using fun a : {a : F // affineCubeModeFactors U root difference (frequency a)} =>
    hrows U (frequency a) (hfrequency a) a.property
  let row : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ := fun a =>
    if ha : affineCubeModeFactors U root difference (frequency a) then b ⟨a, ha⟩ else fun _ => 0
  refine ⟨row, ?_, ?_⟩
  · intro a j s t
    by_cases ha : affineCubeModeFactors U root difference (frequency a)
    · simpa only [row, dite_eq_left ha] using hb ⟨a, ha⟩ j s t
    · simp [row, ha, (Real.exp_pos _).le]
  · intro I p hp hm c x
    unfold affineCubeFourierProjection retainedSiteFourierSum
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : affineCubeModeFactors U root difference (frequency a)
    · rw [ite_eq_left ha, ite_eq_left ha]
      congr 1
      simpa only [row, dite_eq_left ha] using
        layeredCoefficientCharacter_of_site_factorization U root difference D
          (frequency a) (b ⟨a, ha⟩) (hchar ⟨a, ha⟩) p hp hm x
    · simp only [ite_eq_right ha]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Classical

theorem exists_fixed_kernel_site_fourier_projection (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {K₀ : Type*} [Fintype K₀]
    (root₀ : K₀ → ℤ) (difference₀ : Fin q → K₀ → ℤ)
    (a : ℤ) (_ha : a ≠ 0)
    (_hperiod : integerScalarLattice (Fin q) a ≤ (Matrix.of difference₀).mulVecLin.range)
    {P : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card K₀ : ℝ) ≤ P)
    (_hsite : ∀ (s : Finset (Fin q)) k,
      |((affineSite root₀ difference₀ s (some k) : ℤ) : ℝ)| ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ {K : Type*} [Fintype K] (root : K → ℤ) (difference : Fin q → K → ℤ) (e : K₀ → K)
    (_hroot : ∀ k, root (e k) = root₀ k) (_hdifference : ∀ i k, difference i (e k) = difference₀ i k)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t,
      |(frequency a j d t : ℝ)| ≤ Real.exp P),
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
      ∀ {I : Type*} (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
        (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
        (hm : ∀ j d, coefficients (p j) d ∈ U j) (c : F → ℂ) (x : Option K → I → ℝ),
        affineCubeFourierProjection U root difference frequency p c x =
          retainedSiteFourierSum U root difference frequency b c
            (affineCoveredSiteSample U root difference D p hm x) := by
  obtain ⟨A, hA, hcover⟩ := exists_fixed_kernel_geometric_cover m q
  refine ⟨A, hA, ?_⟩
  intro K₀ _ root₀ difference₀ a ha hperiod P hP hK hsite
  obtain ⟨D, hD, hDP, hrows⟩ := hcover root₀ difference₀ a ha hperiod hP hK hsite
  refine ⟨D, hD, hDP, ?_⟩
  intro K _ root difference e hroot hdifference J _ F _ U frequency hfrequency
  choose b hb hchar using fun a : {a : F // affineCubeModeFactors U root difference (frequency a)} =>
    hrows root difference e hroot hdifference U (frequency a) (hfrequency a) a.property
  let row : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ := fun a =>
    if ha : affineCubeModeFactors U root difference (frequency a) then b ⟨a, ha⟩ else fun _ => 0
  refine ⟨row, ?_, ?_⟩
  · intro a j s t
    by_cases ha : affineCubeModeFactors U root difference (frequency a)
    · simpa only [row, dite_eq_left ha] using hb ⟨a, ha⟩ j s t
    · simp [row, ha, (Real.exp_pos _).le]
  · intro I p hp hm c x
    unfold affineCubeFourierProjection retainedSiteFourierSum
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : affineCubeModeFactors U root difference (frequency a)
    · rw [ite_eq_left ha, ite_eq_left ha]
      congr 1
      simpa only [row, dite_eq_left ha] using
        layeredCoefficientCharacter_of_site_factorization U root difference D
          (frequency a) (b ⟨a, ha⟩) (hchar ⟨a, ha⟩) p hp hm x
    · simp only [ite_eq_right ha]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial
open scoped BigOperators Matrix Classical

noncomputable def sectionSiteFrequency {K : Type*} [Fintype K] {m q : ℕ}
    {J : Fin m → Type*}
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ) : ∀ j, Matrix (Finset (Fin q)) (J j) ℤ :=
  fun j => (T j).transpose * Matrix.of (fun e a => frequency j e.val a)

theorem sectionSiteFrequency_bound {K : Type*} [Fintype K] {m q : ℕ} {J : Fin m → Type*}
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ)
    (frequency : ∀ j, (K →₀ ℕ) → J j → ℤ)
    {B C : ℝ} (hC : 0 ≤ C) (hT : ∀ j s, (∑ e, |(T j e s : ℝ)|) ≤ B)
    (hf : ∀ j e, e.degree ≤ j.val + 1 → ∀ a, |(frequency j e a : ℝ)| ≤ C)
    (j : Fin m) (s : Finset (Fin q)) (a : J j) :
    |(sectionSiteFrequency T frequency j s a : ℝ)| ≤ B * C :=
  integer_section_frequency_bound (T j) (Matrix.of (fun e a => frequency j e.val a))
    hC (hT j) (fun e a => hf j e.val e.property a) s a

theorem section_retained_fourier_sum {I K F : Type*} [Fintype K] [Fintype F] {m q : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin q → K → ℤ) (d : ℕ) (hd : 0 < d)
    (T : ∀ j : Fin m, Matrix (BoundedCoefficientExponent K (j.val + 1)) (Finset (Fin q)) ℤ)
    (hT : ∀ j (x : BoundedCoefficientExponent K (j.val + 1) → U j),
      let E := boundedSiteMatrix (j.val + 1) (fun s k => affineSite root difference s (some k))
      matrixModuleAction (fun s e => (E s e : ℝ))
        (matrixModuleAction (fun e s => (T j e s : ℝ))
          (matrixModuleAction (fun s e => (E s e : ℝ)) x)) =
        (d : ℝ) • matrixModuleAction (fun s e => (E s e : ℝ)) x)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (x : Option K → I → ℝ) :
    affineCubeFourierProjection U root difference frequency p c x =
      retainedSiteFourierSum U root difference frequency (fun a => sectionSiteFrequency T (frequency a)) c
        (affineCoveredSiteSample U root difference d p hm x) := by
  unfold affineCubeFourierProjection retainedSiteFourierSum
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : affineCubeModeFactors U root difference (frequency a)
  · rw [ite_eq_left ha, ite_eq_left ha]
    congr 1
    apply layeredCoefficientCharacter_of_site_factorization U root difference d (frequency a)
      (sectionSiteFrequency T (frequency a)) _ p hp hm x
    intro j v hv
    obtain ⟨M, hM⟩ := affineCubeModeFactors_bounded U root difference (frequency a) ha j
    exact integer_section_polynomial_character (U j) (j.val + 1)
      (fun s k => affineSite root difference s (some k)) (T j) d hd (hT j) (frequency a j) M hM v hv
  · simp only [ite_eq_right ha]

end Erdos3.BooleanCubeKernel

end

end OAI
