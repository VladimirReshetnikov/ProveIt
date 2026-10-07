/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedActualProfileControl

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "reference" => allocatedLongJetReference B U b S O
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

noncomputable def allocatedPhysicalLongJetRowBox (T : ℝ) :
    ∀ a : {a // ¬grid a}, Set (CoefficientJetAxisRow O a.val)
  | ⟨⟨j, .inl _⟩, _⟩ => (Metric.closedBall (0 : O j → ℝ) (T * R j) : Set (O j → ℝ))
  | ⟨⟨j, .inr i⟩, _⟩ =>
      (rectangularWeightIndices (fun _ => 0)
        (fun _ : O j => R j * (basisAxisScale (b j) i : ℝ)) T : Set (O j → ℤ))

noncomputable def allocatedPhysicalLongJetBox (T : ℝ) : Set (AllocatedLongJetRows B U b S O) :=
  Set.univ.pi (allocatedPhysicalLongJetRowBox B U b S O T)

theorem allocatedPhysicalLongJetRowBox_measurable (T : ℝ) (a : {a // ¬grid a}) :
    MeasurableSet (allocatedPhysicalLongJetRowBox B U b S O T a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change MeasurableSet (Metric.closedBall (0 : O j → ℝ) (T * R j))
    exact measurableSet_closedBall
  · change MeasurableSet (↑(rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => R j * (basisAxisScale (b j) i : ℝ)) T) : Set (O j → ℤ))
    exact Finset.measurableSet _

theorem allocatedPhysicalLongJetBox_measurable (T : ℝ) :
    MeasurableSet (allocatedPhysicalLongJetBox B U b S O T) :=
  MeasurableSet.univ_pi (allocatedPhysicalLongJetRowBox_measurable B U b S O T)

theorem allocatedPhysicalLongJetRowBox_measure_lt_top (T : ℝ) (a : {a // ¬grid a}) :
    coefficientJetAxisReference O a.val (allocatedPhysicalLongJetRowBox B U b S O T a) < ∞ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change MeasureTheory.volume (Metric.closedBall (0 : O j → ℝ) (T * R j)) < ∞
    exact (isCompact_closedBall (0 : O j → ℝ) (T * R j)).measure_lt_top
  · change Measure.count (↑(rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => R j * (basisAxisScale (b j) i : ℝ)) T) : Set (O j → ℤ)) < ∞
    rw [Measure.count_apply_finset]
    simp

theorem allocatedPhysicalLongJetBox_measure_lt_top (T : ℝ) :
    reference (allocatedPhysicalLongJetBox B U b S O T) < ∞ := by
  unfold allocatedLongJetReference allocatedPhysicalLongJetBox
  rw [Measure.pi_pi]
  exact ENNReal.prod_lt_top (fun a _ => allocatedPhysicalLongJetRowBox_measure_lt_top B U b S O T a)

theorem allocatedPhysicalLongJetBox_of_normalizedCoordinates
    (hR : ∀ j, 0 < R j) {T : ℝ} (hT : 0 ≤ T)
    (z : AllocatedLongJetRows B U b S O)
    (hz : ‖fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1‖ ≤ T) :
    z ∈ allocatedPhysicalLongJetBox B U b S O T := by
  apply Set.mem_univ_pi.mpr
  intro a
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · change ‖(fun o : O j => z ⟨⟨j, .inl i⟩, ha⟩ o) - 0‖ ≤ T * R j
    rw [sub_zero]
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hT (hR j).le)).mpr
    intro o
    have ho : |z ⟨⟨j, .inl i⟩, ha⟩ o / R j| ≤ T :=
      (norm_le_pi_norm (fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1)
        ⟨⟨⟨j, .inl i⟩, ha⟩, o⟩).trans hz
    rw [abs_div, abs_of_pos (hR j)] at ho
    exact (div_le_iff₀ (hR j)).mp ho
  · change z ⟨⟨j, .inr i⟩, ha⟩ ∈ rectangularWeightIndices (fun _ => 0)
      (fun _ : O j => R j * (basisAxisScale (b j) i : ℝ)) T
    apply Fintype.mem_piFinset.mpr
    intro o
    have ho : |((z ⟨⟨j, .inr i⟩, ha⟩ o : ℝ) / (basisAxisScale (b j) i : ℝ)) / R j| ≤ T :=
      (norm_le_pi_norm (fun q : output => allocatedLongJetRealCoordinates B U b S z q / R q.1.val.1)
        ⟨⟨⟨j, .inr i⟩, ha⟩, o⟩).trans hz
    rw [div_div] at ho
    have hh : (0 : ℝ) < basisAxisScale (b j) i := Nat.cast_pos.mpr (basisAxisScale_pos (b j) i)
    obtain ⟨hlo, hhi⟩ := abs_le.mp ho
    have hlo' := (le_div_iff₀ (mul_pos hh (hR j))).mp hlo
    have hhi' := (div_le_iff₀ (mul_pos hh (hR j))).mp hhi
    apply Finset.mem_Icc.mpr
    exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "reference" => allocatedLongJetReference B U b S O
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))

theorem allocatedActiveIntegerPhysicalScale_one_le
    (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1)
    (j : Fin m) (i : Fin (n j)) (ha : ¬grid ⟨j, .inr i⟩) :
    1 ≤ R j * (basisAxisScale (b j) i : ℝ) := by
  have h := allocatedEnormous_constant_width B U b hR S j i (hσ1 j) (Nat.lt_of_not_ge ha)
  have hp : (1 : ℝ) ≤ probabilityProfileLipschitz := probabilityProfileLipschitz_one_le
  nlinarith

theorem allocatedPhysicalLongJetRowBox_measure_bound
    (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1)
    {T : ℝ} (hT : 0 ≤ T) (a : {a // ¬grid a}) :
    (coefficientJetAxisReference O a.val).real (allocatedPhysicalLongJetRowBox B U b S O T a) ≤
      (2 * T + 1) ^ Fintype.card (O a.val.1) * (R a.val.1) ^ Fintype.card (O a.val.1) *
        allocatedLongJetOutputScale B U b S (O := O) a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · have hRj : 0 < R j := hR j
    change MeasureTheory.volume.real (Metric.closedBall (0 : O j → ℝ) (T * R j)) ≤
      (2 * T + 1) ^ Fintype.card (O j) * (R j) ^ Fintype.card (O j) * 1
    rw [mul_one, measureReal_def, Real.volume_pi_closedBall 0 (mul_nonneg hT (hR j).le),
      ENNReal.toReal_ofReal (by positivity), ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [hR j]) _
  · change (Measure.count : Measure (O j → ℤ)).real
      (↑(rectangularWeightIndices (fun _ => 0)
        (fun _ : O j => R j * (basisAxisScale (b j) i : ℝ)) T) : Set (O j → ℤ)) ≤
      (2 * T + 1) ^ Fintype.card (O j) * (R j) ^ Fintype.card (O j) *
        (basisAxisScale (b j) i : ℝ) ^ Fintype.card (O j)
    rw [measureReal_def, Measure.count_apply_finset, ENNReal.toReal_natCast]
    have hscale := allocatedActiveIntegerPhysicalScale_one_le B U b S hR hσ1 j i ha
    simpa only [Finset.prod_const, Finset.card_univ, mul_pow, mul_assoc] using
      rectangularWeightIndices_card_le (fun _ : O j => 0)
        (fun _ => R j * (basisAxisScale (b j) i : ℝ)) (fun _ => hscale) hT

theorem allocatedPhysicalLongJetBox_measure_bound
    (hR : ∀ j, 0 < R j) (hσ1 : ∀ j, σ j ≤ 1) {T : ℝ} (hT : 0 ≤ T) :
    (reference).real (allocatedPhysicalLongJetBox B U b S O T) ≤
      (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
        (∏ q : output, R q.1.val.1) *
        ∏ a, allocatedLongJetOutputScale B U b S (O := O) a := by
  have hc : Fintype.card output ≤ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
    apply Fintype.card_le_of_injective
      (fun q : output => (⟨q.1.val, q.2⟩ : Σ a : LayerSamplerAxis I n, O a.1))
    rintro ⟨⟨a, ha⟩, x⟩ ⟨⟨b, hb⟩, y⟩ h
    cases h
    rfl
  have hs : (∑ a : {a // ¬grid a}, Fintype.card (O a.val.1)) ≤
      Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
    simpa only [Fintype.card_sigma] using hc
  have hprod : (∏ a : {a // ¬grid a}, (R a.val.1) ^ Fintype.card (O a.val.1)) =
      ∏ q : output, R q.1.val.1 := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ]
  calc
    _ = ∏ a : {a // ¬grid a},
        (coefficientJetAxisReference O a.val).real (allocatedPhysicalLongJetRowBox B U b S O T a) := by
      simp only [measureReal_def, allocatedLongJetReference, allocatedPhysicalLongJetBox,
        Measure.pi_pi, ENNReal.toReal_prod]
    _ ≤ ∏ a : {a // ¬grid a}, ((2 * T + 1) ^ Fintype.card (O a.val.1) *
        (R a.val.1) ^ Fintype.card (O a.val.1) * allocatedLongJetOutputScale B U b S (O := O) a) :=
      Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg)
        (fun a _ => allocatedPhysicalLongJetRowBox_measure_bound B U b S O hR hσ1 hT a)
    _ = (2 * T + 1) ^ (∑ a : {a // ¬grid a}, Fintype.card (O a.val.1)) *
        (∏ q : output, R q.1.val.1) * ∏ a, allocatedLongJetOutputScale B U b S (O := O) a := by
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hprod]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hs)
        (Finset.prod_nonneg (fun q _ => (hR q.1.val.1).le)))
      (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))

end Erdos3.VectorPolynomial

end

end OAI
