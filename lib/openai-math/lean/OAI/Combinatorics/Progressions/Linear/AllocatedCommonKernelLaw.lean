import OAI.Combinatorics.Progressions.Estimates.AllocatedCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

theorem allocatedCommonScale_kernel_cutoff {dim : ℕ} [Nonempty (Fin dim)]
    {p c P e E Ebad T : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T)
    (hdim : (dim : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    (hbudget : allocatedKernelPrimitiveBudget p Ebad T ≤ P)
    {M Dwin : ℕ} (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDwinP : (Dwin : ℝ) ≤ Real.exp p) :
    let cutoff := scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(Ebad + 1)))
    0 < cutoff ∧ (cutoff : ℝ) ≤ Real.exp P ∧
      cutoff ≤ (allocatedCommonScale (G := G) B U b hR hσ p c P e E).value := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hPq := (allocatedCommonScaleNumeric_bounds m hp hc hP hE).2.2.2.1
  obtain ⟨hpos, hcut, hscale⟩ := allocatedIdealScale_kernel_cutoff B U b hR hσ
    hp hEbad hT hD he (allocatedSiteKernelMaskLog_nonneg m hP)
    (allocatedReferenceIdealError_nonneg m hD hP hE) hdim hG (hbudget.trans hPq)
    hM hDwin hMT hDwinP
  exact ⟨hpos, hcut.trans (Real.exp_le_exp.mpr hbudget), hscale⟩

theorem allocatedCommonScale_affine_bad_probability [DecidableEq G]
    {dim : ℕ} [Nonempty (Fin dim)] {p c P e E Ebad T : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) (hEbad : 0 ≤ Ebad) (hT : 0 ≤ T)
    (hdim : (dim : ℝ) ≤ p) (hG : (Fintype.card G : ℝ) ≤ p)
    (hcard : dim * (dim + 2) ≤ Fintype.card G) (selection : Fin dim ↪ G)
    (hbudget : allocatedKernelPrimitiveBudget p Ebad T ≤ P)
    (M Dwin : ℕ) (hM : 0 < M) (hDwin : 0 < Dwin)
    (hMT : (M : ℝ) ≤ Real.exp T) (hDwinP : (Dwin : ℝ) ≤ Real.exp p) :
    let S := allocatedCommonScale (G := G) B U b hR hσ p c P e E
    let cutoff := scalarKernelCutoff (Fin dim) G M Dwin (Real.exp (-(Ebad + 1)))
    let hlarge := (allocatedCommonScale_kernel_cutoff B U b hR hσ hp hc hP he hE hEbad hT
      hdim hG hbudget hM hDwin hMT hDwinP).2.2
    ∀ (window : G → ℕ) (hwindow : ∀ g, window g ≤ S.value) (hDwindow : ∀ g, S.value ≤ Dwin * window g)
      (shift : G → ℤ) (moduli : G → Option (Fin dim) → ℕ)
      (residues : ∀ g i, ZMod (moduli g i))
      (hmoduli : ∀ g i, 0 < moduli g i) (hmoduliM : ∀ g i, moduli g i ≤ M),
    (FiniteProbabilityWeights.pi (fun g =>
      affineScalarCubeWindowWeights (Fin dim) S.value (window g) M Dwin (shift g) S.positive
        (hwindow g) (hDwindow g) (moduli g) (residues g) (hmoduli g) (hmoduliM g)
        (scalarKernelCutoff_window_size (Fin dim) G hM hDwin (Real.exp_pos _) hlarge (hDwindow g)))).eventProbability
      (fun x => ¬ GoodScalarKernelTuple selection (1 / (cutoff : ℝ)) cutoff x) ≤ Real.exp (-(Ebad + 1)) := by
  intro S cutoff hlarge window hwindow hDwindow shift moduli residues hmoduli hmoduliM
  exact affineKernel_explicit_probability_le_of_card_le (Fin dim) G
    (by simpa only [Fintype.card_fin] using hcard) selection hM hDwin (Real.exp_pos _) S.positive
    hlarge window hwindow hDwindow shift moduli residues hmoduli hmoduliM

end Erdos3.VectorPolynomial

end

end OAI
