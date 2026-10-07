import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineSourceAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (rowSets : Fin m → Finset (Finset (Fin 1)))

local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))

theorem preparedModularDetector_variable_count {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D) :
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * D := by
  change ((Fintype.card (G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n))) : ℝ) ≤ _
  rw [Fintype.card_sum, Nat.cast_add]
  linarith [hdim.kernel_variables, hdim.tuples]

theorem preparedModularDetector_layer_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D) :
    (∀ j, (Fintype.card (I j) : ℝ) ≤ D) ∧ (∀ j, (n j : ℝ) ≤ D) := by
  constructor
  · intro j
    have hcard : Fintype.card (I j) ≤ Fintype.card (LayerSamplerAxis I n) :=
      Fintype.card_le_of_injective (fun i : I j => (⟨j, Sum.inl i⟩ : LayerSamplerAxis I n))
        (by intro x y h; exact Sum.inl_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
    exact (Nat.cast_le.mpr hcard).trans hdim.axes

  · intro j
    have hcard : Fintype.card (Fin (n j)) ≤ Fintype.card (LayerSamplerAxis I n) :=
      Fintype.card_le_of_injective (fun i : Fin (n j) => (⟨j, Sum.inr i⟩ : LayerSamplerAxis I n))
        (by intro x y h; exact Sum.inr_injective (eq_of_heq (Sigma.mk.inj_iff.mp h).2))
    rw [Fintype.card_fin] at hcard
    exact (Nat.cast_le.mpr hcard).trans hdim.axes

theorem preparedModularDetector_block_card (a : LayerSamplerAxis I n) :
    Fintype.card (B a) ≤ Fintype.card (LayerSamplerVariables G I n B) := by
  let f : B a → LayerSamplerVariables G I n B := fun x =>
    Sum.inr ⟨a, x, ⟨0, by simp [layerSamplerDegree]⟩⟩
  apply Fintype.card_le_of_injective f
  intro x y h
  have hpair := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr_injective h)).2
  exact congrArg Prod.fst hpair

theorem preparedModularDetector_blocks {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (a : LayerSamplerAxis I n) :
    (Fintype.card (B a) : ℝ) ≤ 2 * D :=
  (Nat.cast_le.mpr (preparedModularDetector_block_card (G := G) B a)).trans
    (preparedModularDetector_variable_count B rowSets hdim)

variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem preparedModularDetector_grid_axes {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D) :
    (Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} : ℝ) ≤ D :=
  (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans hdim.axes

theorem preparedModularDetector_natural_volume {P D : ℝ}
    (hP : 0 ≤ P) (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hRone : ∀ j, R j ≤ 1)
    (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedFullGridNaturalVolume B U b S rowSets ≤
      Real.exp (P ^ 2 * (((layerTailDegree m + 1 : ℕ) : ℝ) * P + 1)) := by
  have hrow (j : Fin m) : ((rowSets j).card : ℝ) ≤ P := by
    have hr : ((rowSets j).card : ℝ) ≤ D := by
      simpa only [Fintype.card_coe] using hdim.rows j
    exact hr.trans hDP
  have hvol := allocatedFullGridNaturalVolume_le_exp B U b S rowSets hR
    (P := 0) (L := P) (D := P) (by norm_num) hP hP
    (fun j => by simpa only [Real.exp_zero] using hRone j) hS hrow
  apply hvol.trans (Real.exp_le_exp.mpr ?_)
  have hgrid := (preparedModularDetector_grid_axes B rowSets U b S hdim).trans hDP
  calc
    _ ≤ P * (P * (0 + ((layerTailDegree m + 1 : ℕ) : ℝ) * P + 1)) :=
      mul_le_mul_of_nonneg_right hgrid (by positivity)
    _ = _ := by ring

theorem preparedModularDetector_principal_slots {P D : ℝ}
    (hP : 0 ≤ P) (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) (j : Fin m) (i : Fin (n j)) :
    8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) ≤
      Real.exp (P + 8) := by
  have hc : (Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) ≤ P :=
    (Nat.cast_le.mpr (Finset.card_le_univ _)).trans ((hdim.coefficients j).trans hDP)
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  calc
    _ ≤ 8 * (P + 1) := by linarith
    _ ≤ Real.exp 8 * Real.exp P := mul_le_mul h8 (Real.add_one_le_exp P)
      (by linarith) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem preparedModularDetector_grid_slot_cap {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D) (hDP : D ≤ P) :
    let Qgrid := Real.toNNReal (8 * (D + 1))
    (∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2) : ℝ) + 1) ≤
        (Qgrid : ℝ)) ∧ (Qgrid : ℝ) ≤ Real.exp (P + 8) := by
  have hnonneg : 0 ≤ 8 * (D + 1) := by linarith [hdim.nonneg]
  dsimp only
  rw [Real.coe_toNNReal _ hnonneg]
  constructor
  · intro a
    have hc := (Nat.cast_le.mpr (Finset.card_le_univ
      (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U b S a).1 (allocatedGridIntegerAxis B U b S a).2))).trans
      (hdim.coefficients (allocatedGridIntegerAxis B U b S a).1)
    linarith
  · have hP := hdim.nonneg.trans hDP
    have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
    calc
      _ ≤ 8 * (P + 1) := by linarith
      _ ≤ Real.exp 8 * Real.exp P :=
        mul_le_mul h8 (Real.add_one_le_exp P) (by linarith) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem preparedModularDetector_ambient_count {P : ℝ}
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P) :
    ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ (m : ℝ) * P := by
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ _j : Fin m, P := Finset.sum_le_sum (fun j _ => hJ j)
    _ = _ := by simp

theorem preparedModularDetector_physical_root {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) (hS : (S.value : ℝ) ≤ Real.exp P) :
    allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ Real.exp (2 * P + 8) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ 2 * P :=
    (preparedModularDetector_variable_count B rowSets hdim).trans (by linarith)
  have hvarsExp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp (P + 8) := by
    calc
      _ ≤ 2 * P := hvars
      _ ≤ Real.exp 8 * Real.exp P := mul_le_mul
        (by linarith [Real.add_one_le_exp (8 : ℝ)])
        (by linarith [Real.add_one_le_exp P]) hP (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [allocatedPhysicalRootBudget_zero]
  calc
    _ ≤ Real.exp (P + 8) * Real.exp P :=
      mul_le_mul hvarsExp hS (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem preparedModularDetector_site_radius {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) :
    2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp (2 * P + 8) := by
  apply (allocatedRowSlicedSiteRadius_buffer_le_exp rowSets).trans
  apply Real.exp_le_exp.mpr
  simp only [Fintype.card_fin, Nat.cast_one, mul_one]
  linarith [hdim.degree]

theorem preparedModularDetector_source_numerics (C V : Fin m → ℝ≥0) {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P) (hS : (S.value : ℝ) ≤ Real.exp P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P) :
    AllocatedSourceNumerics B U b S C V (2 * P + 8) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hPQ : P ≤ 2 * P + 8 := by linarith
  have hDQ := hDP.trans hPQ
  have hExp : Real.exp P ≤ Real.exp (2 * P + 8) := Real.exp_le_exp.mpr hPQ
  obtain ⟨hI, hn⟩ := preparedModularDetector_layer_axes B rowSets hdim
  exact {
    nonneg := by linarith
    degree := hdim.degree.trans hDQ
    variable_count := (preparedModularDetector_variable_count B rowSets hdim).trans (by linarith)
    length := hS.trans hExp
    radius_inv := fun j => (hRi j).trans hExp
    width_inv := fun j => (hσi j).trans hExp
    coefficients := fun j => (hdim.coefficients j).trans hDQ
    real_axes := fun j => (hI j).trans hDQ
    integer_axes := fun j => (hn j).trans hDQ
    ambient_axes := fun j => (hJ j).trans hPQ
    profile := hdim.profile.trans (hDQ.trans (by linarith [Real.add_one_le_exp (2 * P + 8)]))
    chart := fun j => (hC j).trans hExp
    covolume := fun j => (hV j).trans hExp
    root := preparedModularDetector_physical_root B rowSets U b S hdim hDP hS }

theorem preparedModularDetector_chart_sum (C : Fin m → ℝ≥0) {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) :
    ((∑ j, C j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp (3 * P) := by
  have hP : 0 ≤ P := hdim.nonneg.trans hDP
  have hPexp : P ≤ Real.exp P := by linarith [Real.add_one_le_exp P]
  have hmexp : (m : ℝ) ≤ Real.exp P := hdim.degree.trans (hDP.trans hPexp)
  push_cast
  calc
    _ ≤ ∑ _j : Fin m, Real.exp P * P := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul (hC j) (hJ j) (Nat.cast_nonneg _) (Real.exp_nonneg _)
    _ = (m : ℝ) * (Real.exp P * P) := by simp
    _ ≤ Real.exp P * (Real.exp P * Real.exp P) := mul_le_mul hmexp
      (mul_le_mul_of_nonneg_left hPexp (Real.exp_nonneg _)) (by positivity) (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem preparedModularDetector_inverse_normalizer (C V : Fin m → ℝ≥0) {P D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B (Fin 1) rowTypes D)
    (hDP : D ≤ P) (hR : ∀ j, 0 < R j) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P) (hS : (S.value : ℝ) ≤ Real.exp P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hC : ∀ j, (C j : ℝ) ≤ Real.exp P) (hV : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hvolume : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j) :
    ‖((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹‖ ≤
      Real.exp ((m * (2 : ℝ)) * (2 * P + 16) * (1 + 4 * (2 * P + 8))) := by
  have hnum := preparedModularDetector_source_numerics B rowSets U b S C V
    hdim hDP hRi hσi hS hJ hC hV
  have h := allocatedProductIdealNormalizer_source_budget B U b S rowSets hR C V hnum hvolume
  simpa only [Fintype.card_fin, pow_one, add_assoc, show (8 : ℝ) + 8 = 16 by norm_num] using h

end Erdos3.VectorPolynomial

end

end OAI
