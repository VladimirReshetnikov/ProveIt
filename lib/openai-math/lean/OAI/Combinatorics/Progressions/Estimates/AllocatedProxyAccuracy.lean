import OAI.Combinatorics.Progressions.Estimates.AllocatedProfileDimensions
import OAI.Combinatorics.Progressions.Geometry.CoefficientSquareSpatialBudget
import OAI.Combinatorics.Progressions.Probability.CoefficientMajorantMassBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

def coefficientErrorAccuracyLog {A : Type*} [Semiring A] (P E : A) : A :=
  coefficientErrorSpatialLog P + coefficientMajorantMassLog P + E + 3

noncomputable def coefficientErrorAccuracy (P E : ℝ) : ℝ :=
  Real.exp (-coefficientErrorAccuracyLog P E)

theorem coefficientErrorAccuracy_bounds {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    0 < coefficientErrorAccuracy P E ∧ coefficientErrorAccuracy P E ≤ 1 ∧
      (coefficientErrorAccuracy P E)⁻¹ = Real.exp (coefficientErrorAccuracyLog P E) := by
  have hs := coefficientErrorSpatialLog_nonneg hP
  have hm := coefficientMajorantMassLog_nonneg hP
  have hlog : 0 ≤ coefficientErrorAccuracyLog P E := by
    unfold coefficientErrorAccuracyLog
    positivity
  refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hlog), ?_⟩
  rw [coefficientErrorAccuracy, ← Real.exp_neg, neg_neg]

theorem coefficientErrorAccuracy_loss_bound {P E S H : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E)
    (hH0 : 0 ≤ H) (hS : S ≤ Real.exp (coefficientErrorSpatialLog P))
    (hH : H ≤ Real.exp (coefficientMajorantMassLog P)) :
    S * (coefficientErrorAccuracy P E * H + 2 * coefficientErrorAccuracy P E +
      coefficientErrorAccuracy P E) ≤ Real.exp (-E) := by
  let a := coefficientErrorAccuracy P E
  have ha : 0 ≤ a := (coefficientErrorAccuracy_bounds hP hE).1.le
  have hmass : 1 ≤ Real.exp (coefficientMajorantMassLog P) :=
    Real.one_le_exp (coefficientMajorantMassLog_nonneg hP)
  have haMass : a ≤ a * Real.exp (coefficientMajorantMassLog P) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass ha
  have h4 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  change S * (a * H + 2 * a + a) ≤ _
  calc
    _ ≤ Real.exp (coefficientErrorSpatialLog P) *
        (a * Real.exp (coefficientMajorantMassLog P) + 2 * a + a) := by gcongr
    _ ≤ Real.exp (coefficientErrorSpatialLog P) *
        (4 * a * Real.exp (coefficientMajorantMassLog P)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (Real.exp_pos _).le
    _ = 4 * (Real.exp (coefficientErrorSpatialLog P) *
        Real.exp (-coefficientErrorAccuracyLog P E) * Real.exp (coefficientMajorantMassLog P)) := by
      unfold a coefficientErrorAccuracy
      ring
    _ = 4 * Real.exp (-E - 3) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      congr 1
      unfold coefficientErrorAccuracyLog
      ring
    _ ≤ Real.exp 3 * Real.exp (-E - 3) := mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem coefficientError_normalized_exp_bound {error E Z : ℝ}
    (herror : error ≤ Real.exp (-(E + 1))) (hZ : 1 / 2 ≤ Z) :
    error / Z ≤ Real.exp (-E) := by
  have hZ0 : 0 < Z := by linarith
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have he : 2 * Real.exp (-(E + 1)) ≤ Real.exp (-E) := by
    calc
      _ ≤ Real.exp 1 * Real.exp (-(E + 1)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (div_le_iff₀ hZ0).mpr
  calc
    error ≤ Real.exp (-(E + 1)) := herror
    _ = Real.exp (-(E + 1)) * 2 * (1 / 2) := by ring
    _ ≤ Real.exp (-E) * (1 / 2) := by nlinarith
    _ ≤ Real.exp (-E) * Z := mul_le_mul_of_nonneg_left hZ (Real.exp_pos _).le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

noncomputable def allocatedCoefficientAccuracyLog (m : ℕ) (p E : ℝ) : ℝ :=
  coefficientErrorAccuracyLog (allocatedComparisonDimension m p + 1) E

noncomputable def allocatedCoefficientAccuracy (m : ℕ) (p E : ℝ) : ℝ :=
  coefficientErrorAccuracy (allocatedComparisonDimension m p + 1) E

theorem allocatedCoefficientAccuracy_bounds (m : ℕ) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    0 < allocatedCoefficientAccuracy m p E ∧ allocatedCoefficientAccuracy m p E ≤ 1 ∧
      (allocatedCoefficientAccuracy m p E)⁻¹ = Real.exp (allocatedCoefficientAccuracyLog m p E) := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  exact coefficientErrorAccuracy_bounds (by positivity) hE

theorem exists_allocatedCoefficientAccuracyLog_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E : ℝ}, 0 ≤ p → 0 ≤ E →
      allocatedCoefficientAccuracyLog m p E ≤ (p + E + a) ^ a := by
  let poly : Polynomial ℕ :=
    coefficientErrorAccuracyLog (allocatedComparisonDimension m Polynomial.X + 1) Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p E hp hE
  have hmono : allocatedCoefficientAccuracyLog m p E ≤
      allocatedCoefficientAccuracyLog m (p + E) (p + E) := by
    have hpq : p ≤ p + E := le_add_of_nonneg_right hE
    have hEq : E ≤ p + E := le_add_of_nonneg_left hp
    unfold allocatedCoefficientAccuracyLog coefficientErrorAccuracyLog coefficientErrorSpatialLog
      coefficientErrorVolumeLog anisotropicSpatialCapLog coefficientMajorantMassLog
      allocatedComparisonDimension
    gcongr
  apply hmono.trans
  simpa [poly, allocatedCoefficientAccuracyLog, coefficientErrorAccuracyLog,
    coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
    coefficientMajorantMassLog, allocatedComparisonDimension, Polynomial.eval₂_pow]
    using hbound (p + E) (add_nonneg hp hE)

theorem exists_allocatedCoefficientAccuracy_budget (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ {p E : ℝ}, 0 ≤ p → 0 ≤ E →
      0 < allocatedCoefficientAccuracy m p E ∧ allocatedCoefficientAccuracy m p E ≤ 1 ∧
        (allocatedCoefficientAccuracy m p E)⁻¹ ≤ Real.exp ((p + E + a) ^ a) := by
  obtain ⟨a, ha, hlog⟩ := exists_allocatedCoefficientAccuracyLog_bound m
  refine ⟨a, ha, ?_⟩
  intro p E hp hE
  obtain ⟨hpos, hone, hinv⟩ := allocatedCoefficientAccuracy_bounds m hp hE
  exact ⟨hpos, hone, hinv.le.trans (Real.exp_le_exp.mpr (hlog hp hE))⟩

theorem allocatedCoefficientErrorAccuracy_bound {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim)) (hdim : dim ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j))
    (X : Type*) [Fintype X] (selection : Fin dim ↪ G) (C : Fin m → ℝ≥0)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    {M period : ℕ} (hM : 0 < M) (hMP : (M : ℝ) ≤ Real.exp p)
    (hperiod : period ≤ M ^ (m + 1))
    {D W L : ℝ} (hD : D ≤ Real.exp p) (hL : 1 ≤ L) (hW : 0 ≤ W) (hWL : W ≤ D * L) :
    let a := allocatedCoefficientAccuracy m p E
    let Aerr := coefficientDeckPeriodCap O Q period
    let Cψ := ((period : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let Vsp := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / L) ^ dim) ^ Fintype.card X
    let Merr := a * Aerr *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    Cψ * (Vsp * (Merr + 2 * a + a)) ≤ Real.exp (-E) := by
  intro a Aerr Cψ Vsp Merr
  let F := allocatedComparisonDimension m p
  let P := F + 1
  have hdim' : Fintype.card (Fin dim) ≤ m + 1 := by simpa only [Fintype.card_fin] using hdim
  have hd := allocatedComparisonDimensions_of_primitive B rows hdim' hinj hp hvars hI hn
  have hP : 0 ≤ P := by dsimp [P, F]; linarith [hd.nonneg]
  have hFP : F ≤ P := by dsimp [P]; linarith
  have hpP : p ≤ P := ((allocatedComparisonDimension_bounds m hp).2.2.1).trans hFP
  have hmP : ((m + 1 : ℕ) : ℝ) ≤ P := by
    have hm := hd.degree
    dsimp [P, F]
    push_cast
    linarith
  have hqP : ((dim + 1 : ℕ) : ℝ) ≤ P := by
    have hq : (dim : ℝ) ≤ F := by simpa only [Fintype.card_fin] using hd.cube
    dsimp [P]
    push_cast
    linarith
  have he := Real.exp_le_exp.mpr hpP
  have hper := coefficientErrorPeriod_exp_sq hP hmP (hMP.trans he) hperiod
  obtain ⟨_hspatial0, hspatial⟩ := coefficientErrorSpatialFactor_exp_bound dim X selection hP hM
    (hMP.trans he) hper hqP (hd.kernel_variables.trans hFP) (hX.trans hpP) hL hW (hD.trans he) hWL
  have hQP (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans ((hJ j).trans hpP)
  have hmass := coefficientMajorantMassFactor_exp_bound O Q J C period
    (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) hP (hd.degree.trans hFP)
    (fun j => (hd.rows j).trans hFP) hQP (fun j => (hJ j).trans hpP) (hd.outputs.trans hFP)
    (fun j => (hC j).trans he) hper
  have hmass0 : 0 ≤ Aerr *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) :=
    mul_nonneg (coefficientDeckPeriodCap_nonneg O Q period) (by positivity)
  have hsmall := coefficientErrorAccuracy_loss_bound hP hE hmass0 hspatial hmass
  calc
    _ = (Cψ * Vsp) * (a * (Aerr *
        (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) + 2 * a + a) := by dsimp [Merr]; ring
    _ ≤ _ := hsmall

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

theorem allocatedCoefficientAccuracy_proxy_error {m dim : ℕ} {G : Type*} [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    {O : Fin m → Type*} [∀ j, Fintype (O j)]
    (rows : ∀ j, O j → Finset (Fin dim)) (hdim : dim ≤ m + 1)
    (hinj : ∀ j, Function.Injective (rows j))
    (C : Fin m → ℝ≥0)
    {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp p)
    {M period : ℕ} (hMP : (M : ℝ) ≤ Real.exp p)
    (hperiod : period ≤ M ^ (m + 1)) :
    let a := allocatedCoefficientAccuracy m p E
    let H := coefficientDeckPeriodCap O Q period *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    a * H + 2 * a + a ≤ Real.exp (-E) := by
  intro a H
  let F := allocatedComparisonDimension m p
  let P := F + 1
  have hdim' : Fintype.card (Fin dim) ≤ m + 1 := by simpa only [Fintype.card_fin] using hdim
  have hd := allocatedComparisonDimensions_of_primitive B rows hdim' hinj hp hvars hI hn
  have hP : 0 ≤ P := by dsimp [P, F]; linarith [hd.nonneg]
  have hFP : F ≤ P := by dsimp [P]; linarith
  have hpP : p ≤ P := ((allocatedComparisonDimension_bounds m hp).2.2.1).trans hFP
  have hmP : ((m + 1 : ℕ) : ℝ) ≤ P := by
    have hm := hd.degree
    dsimp [P, F]
    push_cast
    linarith
  have he := Real.exp_le_exp.mpr hpP
  have hper := coefficientErrorPeriod_exp_sq hP hmP (hMP.trans he) hperiod
  have hQP (j : Fin m) : (Fintype.card (Q j) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (coefficientLatticeBasis_card_le U b hb bW j)).trans ((hJ j).trans hpP)
  have hmass := coefficientMajorantMassFactor_exp_bound O Q J C period
    (Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) hP (hd.degree.trans hFP)
    (fun j => (hd.rows j).trans hFP) hQP (fun j => (hJ j).trans hpP) (hd.outputs.trans hFP)
    (fun j => (hC j).trans he) hper
  have hmass0 : 0 ≤ H :=
    mul_nonneg (coefficientDeckPeriodCap_nonneg O Q period) (by positivity)
  have hsmall := coefficientErrorAccuracy_loss_bound hP hE hmass0
    (Real.one_le_exp (coefficientErrorSpatialLog_nonneg hP)) hmass
  simpa only [one_mul, a, P, F, allocatedCoefficientAccuracy] using hsmall

end Erdos3.VectorPolynomial

end

end OAI
