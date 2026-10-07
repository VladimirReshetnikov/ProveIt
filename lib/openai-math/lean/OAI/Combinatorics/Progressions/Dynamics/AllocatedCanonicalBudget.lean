/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.AllocatedActualCoarseBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedCanonicalNormalizer
import OAI.Combinatorics.Progressions.Estimates.SlicedSourceUniformAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem coefficientDeckPeriodCap_le_exp {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (period : ℕ) {P : ℝ}
    (hperiod : (period : ℝ) ≤ Real.exp P) :
    coefficientDeckPeriodCap O E period ≤
      Real.exp (∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (O j) * P)) := by
  have hrow (j : Fin m) : (period : ℝ) ^ Fintype.card (O j) ≤
      Real.exp (Fintype.card (O j) * P) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hperiod _
  calc
    _ ≤ ∏ j, ∏ _i : E j, Real.exp (Fintype.card (O j) * P) := by
      apply Finset.prod_le_prod₀
      · intro j _
        exact Finset.prod_nonneg (fun _ _ => by positivity)
      · intro j _
        exact Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun _ _ => hrow j)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_sum]

theorem slicedSourcePrefactor_le_exp {m : ℕ} (O E : Fin m → Type*)
    [∀ j, Fintype (O j)] [∀ j, Fintype (E j)] (period axes : ℕ)
    {C M N W P : ℝ} (hC0 : 0 ≤ C) (hC : C ≤ Real.exp N)
    (hM0 : 0 ≤ M) (hM : M ≤ Real.exp W) (hperiod : (period : ℝ) ≤ Real.exp P) :
    C * (M ^ axes * coefficientDeckPeriodCap O E period) ≤
      Real.exp (N + axes * W + ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (O j) * P)) := by
  have hMp : M ^ axes ≤ Real.exp (axes * W) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hM0 hM _
  calc
    _ ≤ Real.exp N * (Real.exp (axes * W) *
        Real.exp (∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (O j) * P))) :=
      mul_le_mul hC
        (mul_le_mul hMp (coefficientDeckPeriodCap_le_exp O E period hperiod)
          (coefficientDeckPeriodCap_nonneg O E period) (Real.exp_nonneg _))
        (mul_nonneg (pow_nonneg hM0 _) (coefficientDeckPeriodCap_nonneg O E period)) (hC0.trans hC)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add, add_assoc]

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

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "naturalVolume" => allocatedFullGridNaturalVolume B U b S rowSets
local notation "gridScale" => allocatedGridJetScale B U b S (O := rowTypes)
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := rowTypes) a)
local notation "radiusVolume" => (∏ t : (Σ a : {a // ¬grid a}, rowTypes (Sigma.fst (Subtype.val a))), R (Sigma.fst (Subtype.val (Sigma.fst t))))

omit [DecidableEq α] in
theorem allocatedIdealNormalizer_row_counts {P : ℝ} (hP : 0 ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P) :
    ((∑ j, Fintype.card (rowTypes j) : ℕ) : ℝ) ≤ m * (2 : ℝ) ^ Fintype.card α ∧
      (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) ≤
        (m * (2 : ℝ) ^ Fintype.card α) * (2 * P) := by
  have hrow (j : Fin m) : (Fintype.card (rowTypes j) : ℝ) ≤ (2 : ℝ) ^ Fintype.card α := by
    have h := Finset.card_le_univ (rowSets j)
    rw [Fintype.card_finset] at h
    rw [Fintype.card_coe]
    exact_mod_cast h
  constructor
  · push_cast
    calc
      _ ≤ ∑ _j : Fin m, (2 : ℝ) ^ Fintype.card α := Finset.sum_le_sum (fun j _ => hrow j)
      _ = _ := by simp
  · have hcount : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes (Sigma.fst a)) : ℝ) =
        ∑ j, ((Fintype.card (I j) : ℝ) + n j) * Fintype.card (rowTypes j) := by
      simp only [Fintype.card_sigma, Fintype.sum_sigma, Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (∑ _a : I j ⊕ Fin (n j), (Fintype.card (rowTypes j) : ℝ)) = _
      simp
    rw [hcount]
    calc
      _ ≤ ∑ _j : Fin m, (2 * P) * (2 : ℝ) ^ Fintype.card α := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul (by linarith [hI j, hn j]) (hrow j) (Nat.cast_nonneg _) (by positivity)
      _ = _ := by simp; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [DecidableEq α] in
theorem allocatedProductIdealNormalizer_early_budget
    (hR : ∀ j, 0 < R j) {P : ℝ} (hP0 : 0 ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp P) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (P + 8) * (1 + 4 * P)) := by
  have hP8 : 0 ≤ P + 8 := by linarith [hP0]
  have hP : P ≤ P + 8 := by linarith
  have hslots (j : Fin m) (i : Fin (n j)) :
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤ Real.exp (P + 8) := by
    have hc : (Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) ≤ P :=
      (Nat.cast_le.mpr (Finset.card_le_univ _)).trans (hcoeff j)
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ 8 * (P + 1) := by linarith
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul h8 (Real.add_one_le_exp P)
        (by linarith [hP0]) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have h := allocatedProductIdealNormalizer_inv_le_exp B U b S rowSets hR hP8
    (fun j => (hV j).trans (Real.exp_le_exp.mpr hP))
    (fun j => (hRi j).trans (Real.exp_le_exp.mpr hP)) hslots
  have hc := allocatedIdealNormalizer_row_counts (I := I) (n := n) rowSets
    hP0 hI hn
  apply h.trans (Real.exp_le_exp.mpr ?_)
  calc
    _ ≤ (m * (2 : ℝ) ^ Fintype.card α) * (P + 8) +
        ((m * (2 : ℝ) ^ Fintype.card α) * (2 * P)) * (2 * (P + 8)) :=
      add_le_add (mul_le_mul_of_nonneg_right hc.1 hP8)
        (mul_le_mul_of_nonneg_right hc.2 (by positivity))
    _ = _ := by ring

omit [DecidableEq α] in
theorem allocatedProductIdealNormalizer_source_budget
    (hR : ∀ j, 0 < R j) (C V : Fin m → ℝ≥0) {P : ℝ}
    (hnum : AllocatedSourceNumerics B U b S C V P)
    (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (P + 8) * (1 + 4 * P)) :=
  allocatedProductIdealNormalizer_early_budget B U b S rowSets hR hnum.nonneg
    hnum.real_axes hnum.integer_axes hnum.coefficients hnum.radius_inv
    (fun j => (hV j).trans (hnum.covolume j))

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

variable (hR : ∀ j, 0 < R j) (C V : Fin m → ℝ≥0) {Pnum : ℝ}
variable (hnum : AllocatedSourceNumerics B U b S C V Pnum)
variable (hV : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hR hnum hV

omit [DecidableEq α] in
theorem allocatedSlicedSourcePrefactor_le_exp
    {Mk period : ℕ} {Pk Pper : ℝ}
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper) :
    ‖inverseNormalizer‖ * ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap rowTypes E period) ≤
    Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)) := by
  exact slicedSourcePrefactor_le_exp rowTypes E period (Fintype.card (LayerSamplerAxis I n))
    (norm_nonneg _) (allocatedProductIdealNormalizer_source_budget B U b S rowSets hR C V hnum hV)
    (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hMk) hperiod

omit [DecidableEq α] in
theorem exists_allocatedSlicedSourceUniformAccuracy
    (O : ℕ) {Pcap Pk Pper target a δ : ℝ} {Mk : ℕ}
    (hPcap : 0 ≤ Pcap) (hPk : 0 ≤ Pk) (hPper : 0 ≤ Pper) (htarget : 0 ≤ target)
    (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (ha : a⁻¹ ≤ Real.exp Pcap) (hδ : δ⁻¹ ≤ Real.exp Pcap) :
    let F := (m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)
    ∃ εgrid : ℝ, 0 < εgrid ∧ εgrid ≤ 1 ∧
      εgrid⁻¹ = Real.exp (slicedJointDensityLogBudget O m Pcap + (target + F) + 1) ∧
      ∀ (ι : Type*) [Fintype ι] (Op : ℝ),
        ∃ εlong P : ℝ, 0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp P ∧
          0 ≤ P ∧ a⁻¹ ≤ Real.exp P ∧ δ⁻¹ ≤ Real.exp P ∧ 4 ≤ Real.exp P ∧
          ∀ period : ℕ, (period : ℝ) ≤ Real.exp Pper →
            ‖inverseNormalizer‖ *
              ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
                coefficientDeckPeriodCap rowTypes E period) *
              (Real.exp (slicedJointDensityLogBudget O m Pcap) * εgrid +
                εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-target) := by
  intro F
  have hF : 0 ≤ F := by
    have hP := hnum.nonneg
    dsimp only [F]
    positivity
  obtain ⟨εgrid, hg0, hg1, hgi, hl⟩ := exists_slicedSourceUniformAccuracy O m hPcap htarget hF ha hδ
  refine ⟨εgrid, hg0, hg1, hgi, ?_⟩
  intro ι hι Op
  obtain ⟨εlong, P, hl0, hl1, hli, hP, haP, hδP, h4, herr⟩ := hl ι Op
  refine ⟨εlong, P, hl0, hl1, hli, hP, haP, hδP, h4, ?_⟩
  intro period hperiod
  apply herr
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (coefficientDeckPeriodCap_nonneg rowTypes E period))
  · exact allocatedSlicedSourcePrefactor_le_exp B U b S rowSets E hR C V hnum hV hMk hperiod

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

include hR hPnum hI hn hcoeff hRi hV

omit [DecidableEq α] in
theorem allocatedSlicedSourceEarlyPrefactor_le_exp
    {Mk period : ℕ} {Pk Pper : ℝ}
    (hMk : (Mk : ℝ) ≤ Real.exp Pk) (hperiod : (period : ℝ) ≤ Real.exp Pper) :
    ‖inverseNormalizer‖ * ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap rowTypes E period) ≤
    Real.exp ((m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)) := by
  exact slicedSourcePrefactor_le_exp rowTypes E period (Fintype.card (LayerSamplerAxis I n))
    (norm_nonneg _) (allocatedProductIdealNormalizer_early_budget B U b S rowSets hR hPnum hI hn hcoeff hRi hV)
    (Nat.cast_nonneg _) (layerKernelIndexBound_le_exp m hMk) hperiod

omit [DecidableEq α] in
theorem exists_allocatedSlicedSourceEarlyUniformAccuracy
    (O : ℕ) {Pcap Pk Pper target a δ : ℝ} {Mk : ℕ}
    (hPcap : 0 ≤ Pcap) (hPk : 0 ≤ Pk) (hPper : 0 ≤ Pper) (htarget : 0 ≤ target)
    (hMk : (Mk : ℝ) ≤ Real.exp Pk)
    (ha : a⁻¹ ≤ Real.exp Pcap) (hδ : δ⁻¹ ≤ Real.exp Pcap) :
    let F := (m * (2 : ℝ) ^ Fintype.card α) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (E j) : ℝ) * (Fintype.card (rowTypes j) * Pper)
    ∃ εgrid : ℝ, 0 < εgrid ∧ εgrid ≤ 1 ∧
      εgrid⁻¹ = Real.exp (slicedJointDensityLogBudget O m Pcap + (target + F) + 1) ∧
      ∀ (ι : Type*) [Fintype ι] (Op : ℝ),
        ∃ εlong P : ℝ, 0 < εlong ∧ εlong ≤ 1 ∧ εlong⁻¹ ≤ Real.exp P ∧
          0 ≤ P ∧ a⁻¹ ≤ Real.exp P ∧ δ⁻¹ ≤ Real.exp P ∧ 4 ≤ Real.exp P ∧
          ∀ period : ℕ, (period : ℝ) ≤ Real.exp Pper →
            ‖inverseNormalizer‖ *
              ((layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
                coefficientDeckPeriodCap rowTypes E period) *
              (Real.exp (slicedJointDensityLogBudget O m Pcap) * εgrid +
                εlong * ∏ _i : ι, Real.exp Op) ≤ Real.exp (-target) := by
  intro F
  have hF : 0 ≤ F := by
    have hP := hPnum
    dsimp only [F]
    positivity
  obtain ⟨εgrid, hg0, hg1, hgi, hl⟩ := exists_slicedSourceUniformAccuracy O m hPcap htarget hF ha hδ
  refine ⟨εgrid, hg0, hg1, hgi, ?_⟩
  intro ι hι Op
  obtain ⟨εlong, P, hl0, hl1, hli, hP, haP, hδP, h4, herr⟩ := hl ι Op
  refine ⟨εlong, P, hl0, hl1, hli, hP, haP, hδP, h4, ?_⟩
  intro period hperiod
  apply herr
  · exact mul_nonneg (norm_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
      (coefficientDeckPeriodCap_nonneg rowTypes E period))
  · exact allocatedSlicedSourceEarlyPrefactor_le_exp B U b S rowSets E hR hPnum hI hn hcoeff hRi hV hMk hperiod

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCutoffAmplitudeLog {A : Type*} [Semiring A]
    (m dim : ℕ) (P : A) : A :=
  (m * 2 ^ dim) * (P + 8) * (1 + 4 * P)

noncomputable def allocatedCutoffLipschitzLog {A : Type*} [Semiring A]
    (m dim : ℕ) (P c : A) : A :=
  allocatedCutoffAmplitudeLog m dim P + 2 * P + 2 * c * (m : A) ^ 3 * (2 ^ dim : A) ^ 2 * P ^ 2

noncomputable def allocatedCutoffFourierLog {A : Type*} [Semiring A]
    (m dim : ℕ) (P c E : A) : A :=
  allocatedCutoffLipschitzLog m dim P c + (m * 2 ^ dim) * P + E + 1

noncomputable def allocatedCutoffSamplingLog {A : Type*} [Semiring A]
    (m dim : ℕ) (P c E S : A) : A :=
  let L := allocatedCutoffFourierLog m dim P c E
  S + 2 * L * (2 * L + 2) ^ 4 + L + (2 * L + 2) ^ 4

theorem allocatedCutoffLipschitzLog_bounds (m dim : ℕ) {P c : ℝ}
    (hP : 0 ≤ P) (hc : 0 ≤ c) :
    0 ≤ allocatedCutoffAmplitudeLog m dim P ∧
      allocatedCutoffAmplitudeLog m dim P ≤ allocatedCutoffLipschitzLog m dim P c ∧
      P ≤ allocatedCutoffLipschitzLog m dim P c ∧
      0 ≤ allocatedCutoffLipschitzLog m dim P c := by
  have ha : 0 ≤ allocatedCutoffAmplitudeLog m dim P := by
    unfold allocatedCutoffAmplitudeLog
    positivity
  have hf : 0 ≤ 2 * c * (m : ℝ) ^ 3 * ((2 : ℝ) ^ dim) ^ 2 * P ^ 2 := by positivity
  dsimp only [allocatedCutoffLipschitzLog]
  exact ⟨ha, by linarith, by linarith, by linarith⟩

theorem allocatedCutoffFourierLog_bounds (m dim : ℕ) {P c E : ℝ}
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hE : 0 ≤ E) :
    let L := allocatedCutoffFourierLog m dim P c E
    0 ≤ L ∧ allocatedCutoffAmplitudeLog m dim P ≤ L ∧
      allocatedCutoffLipschitzLog m dim P c ≤ L ∧
      (m * (2 : ℝ) ^ dim) * P ≤ L ∧ E ≤ L ∧ P ≤ L := by
  obtain ⟨ha, hal, hpl, hl⟩ := allocatedCutoffLipschitzLog_bounds m dim hP hc
  have hd : 0 ≤ (m * (2 : ℝ) ^ dim) * P := by positivity
  dsimp only [allocatedCutoffFourierLog]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem allocatedCutoffSamplingLog_bounds (m dim : ℕ) {P c E S : ℝ}
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hE : 0 ≤ E) (hS : 0 ≤ S) :
    let L := allocatedCutoffFourierLog m dim P c E
    let Q := allocatedCutoffSamplingLog m dim P c E S
    0 ≤ Q ∧ S ≤ Q ∧ L ≤ Q ∧ (2 * L + 2) ^ 4 ≤ Q ∧
      2 * L * (2 * L + 2) ^ 4 + L ≤ Q := by
  have hL := (allocatedCutoffFourierLog_bounds m dim hP hc hE).1
  have hF : 0 ≤ (2 * allocatedCutoffFourierLog m dim P c E + 2) ^ 4 := by positivity
  have hC : 0 ≤ 2 * allocatedCutoffFourierLog m dim P c E *
      (2 * allocatedCutoffFourierLog m dim P c E + 2) ^ 4 := by positivity
  dsimp only [allocatedCutoffSamplingLog]
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem normalizedCutoff_product_bound {a A h u U v V w W : ℝ}
    (ha : a ≤ A) (hu : u ≤ U) (hv : v ≤ V) (hw : w ≤ W)
    (hA : 0 ≤ A) (hh : 0 ≤ h) (hu0 : 0 ≤ u) (hv0 : 0 ≤ v) (hw0 : 0 ≤ w) :
    a * (h * ((u * v) * w)) ≤ A * (h * ((U * V) * W)) := by
  have hU := hu0.trans hu
  have hV := hv0.trans hv
  exact mul_le_mul ha
    (mul_le_mul_of_nonneg_left
      (mul_le_mul (mul_le_mul hu hv hv0 hU) hw hw0 (mul_nonneg hU hV)) hh)
    (mul_nonneg hh (mul_nonneg (mul_nonneg hu0 hv0) hw0)) hA

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

theorem allocatedIdealProfileLog_mono (m : ℕ) {p e p' e' : ℝ}
    (hp : 0 ≤ p) (he : 0 ≤ e) (hpp : p ≤ p') (hee : e ≤ e') :
    allocatedIdealProfileLog m p e ≤ allocatedIdealProfileLog m p' e' := by
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  unfold allocatedIdealProfileLog
  exact mul_le_mul hDD (add_le_add hpp hee) (add_nonneg hp he) (hD.trans hDD)

theorem allocatedSiteErrorFourierOutput_mono (m : ℕ) {p w v p' w' v' : ℝ}
    (hp : 0 ≤ p) (hw : 0 ≤ w) (hv : 0 ≤ v)
    (hpp : p ≤ p') (hww : w ≤ w') (hvv : v ≤ v') :
    allocatedSiteErrorFourierOutput m p w v ≤ allocatedSiteErrorFourierOutput m p' w' v' := by
  have hp' := hp.trans hpp
  have hw' := hw.trans hww
  have hv' := hv.trans hvv
  have hD := (allocatedComparisonDimension_bounds m hp).1
  have hDD := allocatedComparisonDimension_mono m hp hpp
  have hD' := hD.trans hDD
  have hT : allocatedSiteErrorPrimitiveLog m p w v ≤ allocatedSiteErrorPrimitiveLog m p' w' v' := by
    dsimp only [allocatedSiteErrorPrimitiveLog, allocatedErrorPrimitiveLog]
    gcongr
  have hT0 := (allocatedSiteErrorPrimitiveLog_bounds m hp hw hv).1
  have hT' := hT0.trans hT
  have hL : allocatedSiteErrorFourierInput m p w v ≤ allocatedSiteErrorFourierInput m p' w' v' := by
    dsimp only [allocatedSiteErrorFourierInput, allocatedErrorKernelLog]
    gcongr
  have hL0 := (allocatedSiteErrorFourier_budgets m hp hw hv).1
  have hL' := hL0.trans hL
  dsimp only [allocatedSiteErrorFourierOutput]
  gcongr

theorem allocatedSeparatedGeometryLog_nonneg (m : ℕ) {P pa ps w v E : ℝ}
    (hP : 0 ≤ P) (hpa : 0 ≤ pa) (hps : 0 ≤ ps) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E) :
    0 ≤ allocatedSeparatedGeometryLog m P pa ps w v E := by
  have hshift := recenteredShiftLog_nonneg hP (by linarith : 0 ≤ P + 1)
  have hmass := allocatedSiteSpatialMassLog_nonneg (allocatedComparisonDimension_bounds m hpa).1 hw hv
  unfold allocatedSeparatedGeometryLog allocatedOriginalMassLog coefficientErrorVolumeLog
  positivity

theorem allocatedSeparatedGeometryLog_le_original (m : ℕ) {P pa ps w va vs E : ℝ}
    (hpa : 0 ≤ pa) (hw : 0 ≤ w) (_hva : 0 ≤ va) (haps : pa ≤ ps) (hvs : va ≤ vs) :
    allocatedSeparatedGeometryLog m P pa ps w va E ≤ allocatedOriginalGeometryLog m P ps w vs E := by
  have hD := (allocatedComparisonDimension_bounds m hpa).1
  have hDD := allocatedComparisonDimension_mono m hpa haps
  have hD' := hD.trans hDD
  dsimp only [allocatedSeparatedGeometryLog, allocatedOriginalGeometryLog,
    allocatedOriginalMassLog, allocatedSiteSpatialMassLog, coefficientMajorantMassLog]
  gcongr

theorem allocatedCutoffSamplingLog_mono (m dim : ℕ) {P c E S P' c' E' S' : ℝ}
    (hP : 0 ≤ P) (hc : 0 ≤ c) (hE : 0 ≤ E)
    (hPP : P ≤ P') (hcc : c ≤ c') (hEE : E ≤ E') (hSS : S ≤ S') :
    allocatedCutoffSamplingLog m dim P c E S ≤ allocatedCutoffSamplingLog m dim P' c' E' S' := by
  have hP' := hP.trans hPP
  have hc' := hc.trans hcc
  have hL : allocatedCutoffFourierLog m dim P c E ≤ allocatedCutoffFourierLog m dim P' c' E' := by
    dsimp only [allocatedCutoffFourierLog, allocatedCutoffLipschitzLog, allocatedCutoffAmplitudeLog]
    gcongr
  have hL0 := (allocatedCutoffFourierLog_bounds m dim hP hc hE).1
  have hL' := hL0.trans hL
  dsimp only [allocatedCutoffSamplingLog]
  gcongr

section CoverParameter

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedCanonicalCoverParameter (dim A Kraw : ℕ)
    (p cEarly cLate P e E : ℝ) : ℝ :=
  let Eraw := E + 1 + 1 + 4
  let Esite := allocatedOriginalCoverAccuracy P (E + 1 + 1)
  let D := allocatedComparisonDimension m p
  let pNum := allocatedCommonScaleNumeric m p cLate P Eraw
  let pa := allocatedCommonRefinedSourceLog m p cEarly P e 0 Esite
  let ps := allocatedCommonRefinedSourceLog m p cLate P e Eraw Esite
  let w := allocatedSiteKernelMaskLog m P
  let v := allocatedIdealProfileLog m pa e
  let error := allocatedReferenceIdealError m D P Eraw
  let lengthLog := allocatedIdealScaleLog m D pNum e w error
  let gainLog := allocatedProfileGainLog m D P w
  let Pbase := allocatedIdealSourceBudget m D pNum e w error
  let lateLog := allocatedSpatialLateLog (G := G) B Pbase Pbase
  let F := allocatedProfileFourierOutput (allocatedActualProfileInput m D pNum e gainLog lengthLog)
  let Qraw := allocatedSourceSamplingBudget m dim A Pbase (E + 1 + 1) lateLog F
  sourceCoverParameter dim Kraw P pNum Qraw (allocatedSiteErrorFourierOutput m ps w v)
    (allocatedSeparatedGeometryLog m P pa ps w v (E + 1 + 1))

theorem allocatedCanonicalCoverParameter_le_common (dim A Kraw : ℕ)
    {p cEarly cLate P e E : ℝ} (hp : 0 ≤ p) (hcEarly : 0 ≤ cEarly)
    (hc : cEarly ≤ cLate) (hP : 0 ≤ P) (he : 0 ≤ e) (hE : 0 ≤ E) :
    allocatedCanonicalCoverParameter (G := G) B dim A Kraw p cEarly cLate P e E ≤
      allocatedCommonCoverParameter (G := G) B dim A Kraw p cLate P e (E + 1) := by
  let Esite := allocatedOriginalCoverAccuracy P (E + 1 + 1)
  let pa := allocatedCommonRefinedSourceLog m p cEarly P e 0 Esite
  let ps := allocatedCommonRefinedSourceLog m p cLate P e (E + 1 + 1 + 4) Esite
  let w := allocatedSiteKernelMaskLog m P
  let va := allocatedIdealProfileLog m pa e
  let vs := allocatedIdealProfileLog m ps e
  have hEsite : 0 ≤ Esite := by
    have hs := coefficientErrorSpatialLog_nonneg hP
    dsimp [Esite, allocatedOriginalCoverAccuracy]
    linarith
  have hpa : 0 ≤ pa := (allocatedCommonRefinedSourceLog_bounds m hp hcEarly hP he (le_refl 0) hEsite).1
  have hps : 0 ≤ ps := (allocatedCommonRefinedSourceLog_bounds m hp (hcEarly.trans hc) hP he
    (by linarith : 0 ≤ E + 1 + 1 + 4) hEsite).1
  have haps : pa ≤ ps := allocatedCommonRefinedSourceLog_mono m hp hcEarly hP he (le_refl 0)
    le_rfl hc le_rfl le_rfl (by linarith) le_rfl
  have hw : 0 ≤ w := allocatedSiteKernelMaskLog_nonneg m hP
  have hva : 0 ≤ va := allocatedIdealProfileLog_nonneg m hpa he
  have hvs : va ≤ vs := allocatedIdealProfileLog_mono m hpa he haps le_rfl
  have hFourier := allocatedSiteErrorFourierOutput_mono m hps hw hva le_rfl le_rfl hvs
  have hFourier0 : 0 ≤ allocatedSiteErrorFourierOutput m ps w va :=
    hps.trans (allocatedSiteErrorFourier_budgets m hps hw hva).2.2.2.2.1
  have hGeometry := allocatedSeparatedGeometryLog_le_original m hpa hw hva haps hvs (P := P) (E := E + 1 + 1)
  have hGeometry0 := allocatedSeparatedGeometryLog_nonneg m hP hpa hps hw hva (by linarith : 0 ≤ E + 1 + 1)
  unfold allocatedCanonicalCoverParameter allocatedCommonCoverParameter sourceCoverParameter
  dsimp only
  change _ + (allocatedSiteErrorFourierOutput m ps w va) ^ 2 +
      (allocatedSeparatedGeometryLog m P pa ps w va (E + 1 + 1)) ^ 2 ≤
    _ + (allocatedSiteErrorFourierOutput m ps w vs) ^ 2 +
      (allocatedOriginalGeometryLog m P ps w vs (E + 1 + 1)) ^ 2
  gcongr

end CoverParameter

theorem exists_allocatedCanonicalCoverThreshold_bound (m dim A Kraw Ksite : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧
    ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] {p cEarly cLate P e E : ℝ},
      0 ≤ p → 0 ≤ cEarly → cEarly ≤ cLate → 0 ≤ P → 0 ≤ e → 0 ≤ E →
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
      (allocatedCanonicalCoverParameter (G := G) B dim A Kraw p cEarly cLate P e E + Ksite) ^ Ksite ≤
        (p + cLate + P + e + E + a) ^ a := by
  obtain ⟨b, hb, hbound⟩ := exists_allocatedCommonCoverThreshold_bound m dim A Kraw Ksite
  let a := b + 2
  have ha : 2 ≤ a := by dsimp [a]; omega
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ p cEarly cLate P e E hp hcEarly hc hP he hE hvars
  have hparam := allocatedCanonicalCoverParameter_le_common (G := G) B dim A Kraw hp hcEarly hc hP he hE
  have hparam0 : 0 ≤ allocatedCanonicalCoverParameter (G := G) B dim A Kraw p cEarly cLate P e E :=
    zero_le_one.trans (sourceCoverParameter_bounds dim Kraw hP).1
  have hfirst := pow_le_pow_left₀ (add_nonneg hparam0 (Nat.cast_nonneg Ksite))
    (add_le_add hparam (le_refl (Ksite : ℝ))) Ksite
  have hsecond := hbound B hp (hcEarly.trans hc) hP he (show 0 ≤ E + 1 by linarith) hvars
  have hbase : p + cLate + P + e + (E + 1) + b ≤ p + cLate + P + e + E + a := by
    dsimp [a]
    push_cast
    linarith
  have hbase1 : 1 ≤ p + cLate + P + e + E + (a : ℝ) := by
    have har : (2 : ℝ) ≤ a := Nat.cast_le.mpr ha
    linarith
  have hcLate := hcEarly.trans hc
  exact ((hfirst.trans hsecond).trans (pow_le_pow_left₀ (by positivity) hbase b)).trans
    (pow_le_pow_right₀ hbase1 (by dsimp [a]; omega))

theorem exists_regularizedCanonicalCoverThreshold_bound (m dim A₀ Kraw Ksite : ℕ) (A T : ℝ≥0) :
    ∃ a : ℕ, 2 ≤ a ∧
    ∀ {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
      (B : LayerSamplerAxis I n → Type*) [∀ i, Fintype (B i)]
      {p cEarly cLate P E : ℝ}, 0 ≤ p → 0 ≤ cEarly → cEarly ≤ cLate → 0 ≤ P → 0 ≤ E →
      dim ≤ m + 1 → (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p →
      (∀ j, (Fintype.card (I j) : ℝ) ≤ p) → (∀ j, (n j : ℝ) ≤ p) →
      (allocatedCanonicalCoverParameter (G := G) B dim A₀ Kraw p cEarly cLate P
        (allocatedCommonSmoothingLog B dim A T p P E) E + Ksite) ^ Ksite ≤
        (p + cLate + P + E + a) ^ a := by
  obtain ⟨a, ha, hbound⟩ := exists_fixedRegularizedCommonCoverThreshold_bound m dim A₀ Kraw Ksite A T
  refine ⟨a, ha, ?_⟩
  intro G _ I _ n B _ p cEarly cLate P E hp hcEarly hc hP hE hdim hvars hI hn
  have he := allocatedCommonSmoothingLog_nonneg B dim A T hp hP hE
  have hparam := allocatedCanonicalCoverParameter_le_common (G := G) B dim A₀ Kraw hp hcEarly hc hP he hE
  have hparam0 : 0 ≤ allocatedCanonicalCoverParameter (G := G) B dim A₀ Kraw p cEarly cLate P
      (allocatedCommonSmoothingLog B dim A T p P E) E :=
    zero_le_one.trans (sourceCoverParameter_bounds dim Kraw hP).1
  exact (pow_le_pow_left₀ (add_nonneg hparam0 (Nat.cast_nonneg Ksite))
    (add_le_add hparam (le_refl (Ksite : ℝ))) Ksite).trans
      (hbound B hp (hcEarly.trans hc) hP hE hdim hvars hI hn)

end Erdos3.VectorPolynomial

end

end OAI
