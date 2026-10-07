import OAI.Combinatorics.Progressions.Dynamics.AllocatedCanonicalBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_buffer_le_exp (rowSets : Fin m → Finset (Finset α)) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤
      Real.exp (((m : ℝ) + 2) * Fintype.card α + m + 4) := by
  let A : ℝ := ((m : ℝ) + 2) * Fintype.card α + 3
  have hT : 0 ≤ partitionedIdealRadius α m + 1 := by
    have := partitionedIdealRadius_nonneg α m
    positivity
  have hr : (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ 1 + m * idealSiteBoxRadius α m := by
    change 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1) ≤ _
    apply add_le_add_right
    calc
      _ ≤ ∑ _j : Fin m, idealSiteBoxRadius α m := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ hT
        exact_mod_cast (Finset.card_le_univ (rowSets j)).trans_eq (Fintype.card_finset (α := α))
      _ = _ := by simp
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hone : 1 ≤ Real.exp A := Real.one_le_exp_iff.mpr hA
  calc
    _ ≤ 2 + m * (2 * idealSiteBoxRadius α m) := by nlinarith only [hr]
    _ ≤ 2 + m * Real.exp A := by
      gcongr
      exact idealSiteBoxRadius_buffer_le_exp α m
    _ ≤ ((m : ℝ) + 2) * Real.exp A := by nlinarith only [hone]
    _ ≤ Real.exp ((m : ℝ) + 1) * Real.exp A := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      simpa only [add_assoc, one_add_one_eq_two] using Real.add_one_le_exp ((m : ℝ) + 1)
    _ = _ := by rw [← Real.exp_add]; congr 1; dsimp [A]; ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
variable (E : Fin m → Type*) [∀ j, Fintype (E j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) {Pnum : ℝ} (hPnum : 0 ≤ Pnum)
variable (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum) (hn : ∀ j, (n j : ℝ) ≤ Pnum)
variable (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
  (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
variable (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp Pnum)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "outputs" => (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a)))

include hR hPnum hI hn hcoeff hRi hV in
omit [DecidableEq α] in
theorem allocatedAffineSourceEarly_error_budget
    {Mk period : ℕ} {Pk Pper Prho target Op : ℝ}
    (hPk : 0 ≤ Pk) (hPper : 0 ≤ Pper) (hPrho : 0 ≤ Prho) (htarget : 0 ≤ target)
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper)
    (ρ : ℝ≥0) (hρ : (ρ : ℝ)⁻¹ ≤ Real.exp Prho) :
    let F := (m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)
    let Dout := (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ)
    let Dgrid := (Fintype.card (LayerSamplerAxis I n) : ℝ)
    let Pbox := ((m : ℝ) + 2) * Fintype.card α + m + 4
    let εgrid := Real.exp (-(Dout * Prho + (target + F) + 1))
    let Gcost := Dgrid * max Op 0
    let εlong := Real.exp (-(Gcost + (target + F) + 1))
    let Plong := Pbox + Prho + Gcost + (target + F) + 2
    0 < εgrid ∧ εgrid ≤ 1 ∧ εgrid⁻¹ = Real.exp (Dout * Prho + (target + F) + 1) ∧
      0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp Plong ∧ 0 ≤ Plong ∧
      2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Plong ∧
      (ρ : ℝ)⁻¹ ≤ Real.exp Plong ∧
      ‖inverseNormalizer‖ *
        ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
          coefficientDeckPeriodCap rowTypes E period) *
        ((ρ⁻¹ ^ Fintype.card outputs : ℝ≥0) * εgrid +
          εlong * ∏ _a : {a // grid a}, Real.exp Op) ≤ Real.exp (-target) := by
  intro F Dout Dgrid Pbox εgrid Gcost εlong Plong
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hbox : 0 ≤ Pbox := by dsimp only [Pbox]; positivity
  have hout : (Fintype.card outputs : ℝ) ≤ Dout := by
    apply Nat.cast_le.mpr
    apply Fintype.card_le_of_injective (fun a : outputs =>
      (⟨a.1.val, a.2⟩ : Σ a : LayerSamplerAxis I n, rowTypes a.1))
    rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ heq
    cases heq
    rfl
  have hg : (Fintype.card {a // grid a} : ℝ) ≤ Dgrid := by
    change (Fintype.card {a // grid a} : ℝ) ≤ (Fintype.card (LayerSamplerAxis I n) : ℝ)
    exact_mod_cast Fintype.card_subtype_le grid
  have hc0 : 0 ≤ ‖inverseNormalizer‖ *
      ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
        coefficientDeckPeriodCap rowTypes E period) :=
    mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (coefficientDeckPeriodCap_nonneg rowTypes E period))
  obtain ⟨hg0, hg1, hgi, hl0, hl1, hli, hp, hbp, hrp, herr⟩ :=
    affineSourceAccuracy_budget (ι := {a // grid a}) (κ := outputs)
      (Nat.cast_nonneg _) (Nat.cast_nonneg _) hPrho hbox htarget hF hout hg ρ hρ hc0
      (allocatedSlicedSourceEarlyPrefactor_le_exp B U b S rowSets E hR hPnum hI hn hcoeff hRi hV hMk hperiod)
  exact ⟨hg0, hg1, hgi, hl0, hl1, hli, hp,
    (allocatedRowSlicedSiteRadius_buffer_le_exp rowSets).trans (Real.exp_le_exp.mpr hbp), hrp, herr⟩

end Erdos3.VectorPolynomial

end

end OAI
