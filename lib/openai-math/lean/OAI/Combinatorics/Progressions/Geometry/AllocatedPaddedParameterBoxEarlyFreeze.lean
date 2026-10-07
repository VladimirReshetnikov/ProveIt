import OAI.Combinatorics.Progressions.Dynamics.PreparedFreezingEarlyLogBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedPaddedRecoveredPreparedFreeze
import OAI.Combinatorics.Progressions.Lattices.LayerSamplerIntegerBox

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_freeze_allocated_padded_parameter_box
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    (hδbudget : δ ≤ gain / (128 * ((D : ℝ) + 1) * (A.kernel.lip + 1)))
    {Pearly : ℝ}
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (hinflation : ∀ j,
      (32 * ((D : ℝ) + 1) * (A.kernel.lip + 1) * ((q : ℝ) + 1) / gain) *
        (Fintype.card (L.pad q j).Coord : ℝ) * C j ≤ Real.exp Pearly)
    (score : integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (u.val k : ℝ)) := by
  classical
  have hLip : 0 ≤ (A.kernel.lip : ℝ) := NNReal.coe_nonneg _
  let C' : Fin q → ℝ := fun j =>
    (32 * ((D : ℝ) + 1) * (A.kernel.lip + 1) * ((q : ℝ) + 1) / gain) *
      (Fintype.card (L.pad q j).Coord : ℝ) * C j
  have hC' : ∀ j, 0 ≤ C' j := by
    intro j
    dsimp [C']
    exact mul_nonneg (mul_nonneg (div_nonneg (by positivity) hgain.le)
      (Nat.cast_nonneg _)) (hC j)
  have hbud := preparedFreezingRadiusBudget_of_inflated_chart
    (fun j => Fintype.card (L.pad q j).Coord) (fun j => Fintype.card (I j)) C R
    hLip hgain hgain1 (hearly C' hC' hinflation) hδbudget
  have hbox : ∀ (u : integerBox sides) k,
      |(u.val k : ℝ)| ≤ layerSamplerBox B U b S k := by
    intro u k
    have hu := (mem_integerBox sides u.val).mp u.property k
    have h0 : (0 : ℝ) ≤ u.val k := by exact_mod_cast hu.1
    rw [abs_of_nonneg h0]
    have hk : layerSamplerBox B U b S k = (sides k : ℝ) := by cases k <;> rfl
    rw [hk]
    exact_mod_cast hu.2.le
  have hinside : ∀ u : integerBox sides,
      integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val ∈ (integerBox N : Set (X → ℤ)) := by
    intro u
    rw [integerAffineMap_jointIntegerFrame]
    exact narrow_jointIntegerPhysicalSite_mem_box
      (allocatedPhysicalRootBudget_nonneg B U b S (fun _ => 0)) hτ hτhalf hξ1 u.val
      (allocatedParameterBox_root_bound B U b S u) N hN hsize z
  apply F.exists_freeze_allocated_padded_recovered_sample L hmq B U b hb o S hR hσ ip hip c₀ err
    hprepare hm hp hσ1 C hC hchart c z.1.val z.2.val sample read hread hδ hgain
    (integerBox N) herr _ _ Subtype.val hbox hinside score hscoreBound hscore
  · simpa only [mul_assoc] using hbud.1
  · simpa only [mul_assoc] using hbud.2

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G]
variable (L : RankPreparationFamily X (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (Deck j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_freeze_allocated_padded_parameter_box_of_early_bounds
    {A : PolynomialPatch X s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial X ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial X ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
    (hread : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      (fun j => (L.pad q j).poly) hm c z.1.val z.2.val sample read)
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain)
    (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (A.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (score : integerBox (Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)) → ℝ) (hscoreBound : ∀ u, |score u| ≤ 1)
    (hscore : gain / 2 ≤ 𝔼 u, score u * A.value
      (fun x => (integerAffineMap (fun x k => jointIntegerFrame (z.1.val,z.2.val) (some k) x)
        (jointIntegerFrame (z.1.val,z.2.val) none) u.val x : ℝ))) :
    ∃ A' : PolynomialPatch Vars s E,
      A'.kernel.lip = A.kernel.lip ∧
      (∀ i, A'.weight i = A.weight (i.natAdd D)) ∧
      7 * gain / 16 ≤ 𝔼 u, score u * A'.value (fun k => (u.val k : ℝ)) := by
  have hδbudget := (preparedFreezingEarlyLogBudget (N := 0) (C := 0)
    hp0 (NNReal.coe_nonneg A.kernel.lip) le_rfl hDlog hqlog hLlog
    (by simpa only [Nat.cast_zero] using Real.exp_nonneg p) (Real.exp_nonneg p) hgainlog hδearly).2
  have hinflation : ∀ j,
      (32 * ((D : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) * ((q : ℝ) + 1) / gain) *
        (Fintype.card (L.pad q j).Coord : ℝ) * C j ≤ Real.exp Pearly := by
    intro j
    exact ((preparedFreezingEarlyLogBudget hp0 (NNReal.coe_nonneg A.kernel.lip)
      (hC j) hDlog hqlog hLlog (hNlog j) (hClog j) hgainlog hδearly).1).trans
      (Real.exp_le_exp.mpr hPearly)
  exact F.exists_freeze_allocated_padded_parameter_box L hmq B U b hb o S hR hσ ip hip c₀ err
    hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize z sample read hread
    hδ hgain hgain1 herr hδbudget hearly hinflation score hscoreBound hscore

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
