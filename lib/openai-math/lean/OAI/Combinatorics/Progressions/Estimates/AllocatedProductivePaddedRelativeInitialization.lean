import OAI.Combinatorics.Progressions.Dynamics.AllocatedProductivePathPullback
import OAI.Combinatorics.Progressions.Dynamics.RelativeFrozenPatchChildBudget
import OAI.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
import OAI.Combinatorics.Progressions.Geometry.AllocatedPaddedParameterBoxEarlyFreeze
import OAI.Combinatorics.Progressions.Sampling.AllocatedProductiveRelativeScore
import OAI.Combinatorics.Progressions.Sampling.AllocatedSamplerRelativeInduction

namespace OAI

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E : ℕ} {X G : Type} [Fintype X] [Fintype G] [Nonempty G]
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
theorem exists_relative_child_of_allocated_padded_recovery
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
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (hscore : gain / 2 ≤ 𝔼 u : integerBox sides, (f u.val-a) * A.value
      (fun x => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) x : ℝ))) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  have ha0 : 0 ≤ a := (Real.exp_pos _).le.trans ha
  have ha1 : a ≤ 1 := haΛ.trans hΛ
  have hunit : ∀ u : integerBox sides, |f u.val-a| ≤ 1 := by
    intro u
    have hu := hf u.val u.property
    exact abs_le.mpr ⟨by linarith [hu.1], by linarith [hu.2]⟩
  obtain ⟨tail, hLip, hweight, htailScore⟩ :=
    F.exists_freeze_allocated_padded_parameter_box_of_early_bounds L hmq B U b hb o S hR hσ
      ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize z
      sample read hread hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog
      hgainlog hδearly hPearly hearly (fun u => f u.val-a) hunit
      (by simpa only [integerAffineMap_jointIntegerFrame] using hscore)
  have hchildComplex : relativePatchComplexity tail ≤ pchild :=
    (relativePatchComplexity_tail_le A tail hLip).trans hA
  have hchildStage : relativePatchDistinctWeights tail ≤ stage :=
    relativePatchDistinctWeights_tail_le A tail hDpos F.weights hrest hweight hstage
  have hchildScore : Real.exp (-pchild) ≤ relativePatchBoxScore sides f a tail := by
    apply (relativeFrozenPatch_child_score_budget hgainlog hpchild).trans
    have hsum := Finset.sum_subtype (F := inferInstanceAs (Fintype (integerBox sides)))
      (integerBox sides) (fun _ => Iff.rfl)
      (fun x => (f x-a) * tail.value (fun k => (x k : ℝ)))
    simpa only [relativePatchBoxScore, Finset.expect_eq_sum_div_card,
      Finset.card_univ, Fintype.card_coe, ← hsum] using htailScore
  exact exists_allocatedSampler_relative_induction B U b S ih hp2 (by linarith)
    ha haΛ hΛ habsolute hDim H hH hHcut f hf hfree tail hchildComplex hchildStage hchildScore

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
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

attribute [local irreducible] integerBox

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_allocated_fin_padded_recovery
    {A : PolynomialPatch (Fin nX) s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : (Fin nX) → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
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
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Vars → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox sides, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox sides ∧ f x ≠ 0} (s+2))
    (hscore : gain / 2 ≤ 𝔼 u : integerBox sides, (f u.val-a) * A.value
      (fun x => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) x : ℝ))) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  exact F.exists_relative_child_of_allocated_padded_recovery
    (X := Fin nX) (G := G) (m := m) (q := q) (s := s) (D := D) (E := E)
    (A := A) (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize
    ⟨⟨z.1.val, by simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox]
      using z.1.property⟩, z.2⟩
    sample read hread hδ hgain hgain1
    (fun x hx i => herr x (by simpa only [mem_integerBox] using hx) i) hp0 hDlog hqlog hLlog hNlog hClog
    hgainlog hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim
    H hH hHcut hDpos hrest hA hstage f hf hfree hscore

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
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

attribute [local irreducible] RankPreparationFamily.pad integerBox

include hmq in
omit [∀ j, Fintype (Deck j)] in
theorem exists_relative_child_of_productive_padded_recovery
    {A : PolynomialPatch (Fin nX) s (D + E)} (F : A.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (c : ∀ j, U j) (N : (Fin nX) → ℕ) (hN : ∀ x, 0 < N x)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (z : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := Vars) I n)
    (read : AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
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
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff cost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff cost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p+2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < A.weight (i.natAdd D))
    (hA : relativePatchComplexity A ≤ pchild)
    (hstage : relativePatchDistinctWeights A ≤ stage+1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s+2))
    (hproductive : AllocatedPathProductivity B U b S N
      (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N)
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (relativePatchSourceTest N f a A) gain z) :
    ∃ fixed : {k : Vars // ¬H ≤ sides k} → ℤ,
      (∀ k, 0 ≤ fixed k ∧ fixed k < sides k) ∧
      RelativePatchSliceConclusion s
        (fun k : {k : Vars // H ≤ sides k} => sides k)
        (fun x => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ sides k) x fixed) (z.1.val,z.2.val)))
        ((1-discount) ^ (stage+1) * Λ) (d₀+s*E) (cost pchild) := by
  refine F.exists_relative_child_of_allocated_padded_recovery
    (X := Fin nX) (G := G) (m := m) (q := q) (s := s) (D := D) (E := E)
    (A := A) (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart c N hN hτ hτhalf hξ1 hsize
    ⟨⟨z.1.val, by
      simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.1.property⟩, z.2⟩
    sample read hread hδ hgain hgain1
    (fun x hx i => herr x (by simpa only [mem_integerBox] using hx) i) hp0 hDlog hqlog hLlog hNlog hClog
    hgainlog hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim
    H hH hHcut hDpos hrest hA hstage
    (fun u => f (jointIntegerPhysicalSite u (z.1.val,z.2.val))) ?_ ?_ ?_
  · exact hproductive.pullback_mem_Icc (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S) hf
  · exact hproductive.pullback_apFree (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S)
      (by omega : 2 ≤ s + 2) hfree
  · exact hproductive.relativePatch_child_score (I := I) (n := n) (B := B)
      (J := fun j => (L.pad q j).Coord) (U := U) (b := b) (S := S)

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

attribute [local irreducible] integerBox

include hmq in

theorem returned_fibers_of_productive_padded_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (productive : Finset A.Path)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
 :
    ∀ z ∈ productive, ∃ (fixed : {k : Vars // ¬H ≤ A.sides k} → ℤ),
      (∀ k, 0 ≤ fixed k ∧ fixed k < (A.sides k.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun k : {k : Vars // H ≤ A.sides k} => A.sides k.val)
        (fun u => f (jointIntegerPhysicalSite
          (finiteSplitPoint (fun k : Vars => H ≤ A.sides k) u fixed) (z.1.val,z.2.val)))
        ((1 - discount) ^ (stage + 1) * Λ) (d₀ + s * E) (childCost pchild) := by
  intro z hz
  let z' : trimmedIntegerBox N (spatialTrimMargin τ N) ×
      rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n))
          (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 :=
    ⟨⟨z.1.val, by
      simpa only [trimmedIntegerBox, Finset.mem_image, mem_integerBox] using z.1.property⟩,
      ⟨z.2.val, by
      simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
        using z.2.property⟩⟩
  have hprod : AllocatedPathProductivity B U b S N
      (narrowTrimmedSpatialWidths (G := G)
        (J := PrincipalTupleIndex B (layerSamplerDegree I n))
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N)
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (relativePatchSourceTest N f a oldPatch) gain z' := by
    exact hproductive ⟨z,hz⟩
  exact F.exists_relative_child_of_productive_padded_recovery
    (m := m) (q := q) (s := s) (D := D) (E := E) (G := G)
    (I := I) (Deck := Deck) (n := n) (R := R) (σ := σ) (A := oldPatch)
    (τ := τ) (ξ := ξ) (δ := δ) (gain := gain) (p := p) (Pearly := Pearly)
    (n₀ := n₀) (stage := stage) (d₀ := d₀) (discount := discount)
    (cutoff := cutoff) (cost := childCost) (pchild := pchild) (a := a) (Λ := Λ)
    L hmq B U b hb o S hR hσ
    ip hip c₀ err hprepare hm hp hσ1 C hC hchart centerLift N A.size_pos A.trim_pos
    hτhalf hξ1 hsize
    z' (sample ⟨z,hz⟩) (read ⟨z,hz⟩) (hread ⟨z,hz⟩)
    hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog hδearly hPearly hearly
    ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos hrest hA hstage
    f hf hfree hprod

end Erdos3.PolynomialPatch.LowestLayerModel

end

section

namespace Erdos3.PolynomialPatch.LowestLayerModel
open VectorPolynomial Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators TensorProduct Classical

variable {m q s D E nX : ℕ} {G : Type} [Fintype G] [Nonempty G]
variable (L : RankPreparationFamily (Fin nX) (Fin D) m) (hmq : m ≤ q)
variable {I Deck : Fin q → Type} [∀ j, Fintype (I j)]
variable {n : Fin q → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ ((L.pad q j).Coord → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin q → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (L.pad q j).Coord) (euclideanSubspace (U j)))]
local notation "Vars" => LayerSamplerVariables G I n B
local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)

include hmq in

theorem exists_normalizedProblem_of_productive_padded_relative_induction
    {oldPatch : PolynomialPatch (Fin nX) s (D + E)} (F : oldPatch.LowestLayerModel m)
    (ip : Fin D → MvPolynomial (Fin nX) ℤ) (hip : ∀ i, (ip i).totalDegree ≤ m)
    (c₀ : Fin D → ℝ) (err : VectorPolynomial (Fin nX) ℝ (Fin D → ℝ))
    (hprepare : VectorPolynomial.ofCoordinates (Pi.basisFun ℝ (Fin D)) F.normalizedOrigin =
      L.polynomial + integerCoordinates ip + (1 ⊗ₜ[ℝ] c₀) + err)
    (hm : ∀ j d, coefficients (L.pad q j).poly d ∈ U j)
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (L.pad q j).poly)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin q → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (N : Fin nX → ℕ) {τ ξ : ℝ} (hτhalf : τ ≤ 1 / 2) (hξ1 : ξ ≤ 1)
    (hsize : ∀ x, 4 ≤ τ * (N x : ℝ))
    (stride : Fin nX → ℕ)
    (cells : Finset (ColumnResiduePattern (Option Vars) (Fin nX) stride))
    (center : CoefficientTorus (K := Vars) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N
      (fun j => (L.pad q j).poly) hm τ ξ stride cells center)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) (hmass : 0 < A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := Vars) I n)
    (read : productive → AllocatedActualCoefficientIndex G (Fin nX) I Deck n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
        (fun j => (L.pad q j).poly) hm centerLift z.val.1.val z.val.2.val (sample z) (read z))
    {δ gain : ℝ} (hδ : 0 ≤ δ) (hgain : 0 < gain) (hgain1 : gain ≤ 1)
    (herr : ∀ x ∈ integerBox N, ∀ i, |eval (fun z => (x z : ℝ)) err i| ≤ δ)
    {p Pearly : ℝ} (hp0 : 0 ≤ p)
    (hDlog : (D : ℝ) ≤ Real.exp p) (hqlog : (q : ℝ) ≤ Real.exp p)
    (hLlog : (oldPatch.kernel.lip : ℝ) ≤ Real.exp p)
    (hNlog : ∀ j, (Fintype.card (L.pad q j).Coord : ℝ) ≤ Real.exp p)
    (hClog : ∀ j, C j ≤ Real.exp p) (hgainlog : Real.exp (-p) ≤ gain)
    (hδearly : δ ≤ Real.exp (-(3 * p + 130)))
    (hPearly : 6 * p + 35 ≤ Pearly)
    (hearly : ∀ C' : Fin q → ℝ, (∀ j, 0 ≤ C' j) →
      (∀ j, C' j ≤ Real.exp Pearly) →
      ∀ j, C' j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {n₀ stage d₀ : ℕ} {discount : ℝ} {cutoff childCost : ℝ → ℝ}
    (ih : RelativePatchInductionRule s n₀ stage discount cutoff childCost)
    {pchild a Λ : ℝ} (hp2 : 2 ≤ p) (hpchild : p + 2 ≤ pchild)
    (ha : Real.exp (-p) ≤ a) (haΛ : a ≤ Λ) (hΛ : Λ ≤ 1)
    (habsolute : RelativePatchAbsoluteRule s n₀ p a Λ d₀)
    (hDim : (Fintype.card Vars : ℝ) ≤ pchild)
    (H : ℕ) (hH : H ≤ S.value) (hHcut : Real.exp (cutoff pchild) ≤ H)
    (hDpos : 0 < D) (hrest : ∀ i : Fin E, m < oldPatch.weight (i.natAdd D))
    (hA : relativePatchComplexity oldPatch ≤ pchild)
    (hstage : relativePatchDistinctWeights oldPatch ≤ stage + 1)
    (f : (Fin nX → ℤ) → ℝ)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1)
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2))
    (hproductive : ∀ z : productive,
      AllocatedPathProductivity B U b S N A.widths A.bases
        (relativePatchSourceTest N f a oldPatch) gain z.val)
    (hdiscount : discount ∈ Set.Icc (0 : ℝ) 1)
    (hchildCost : 0 ≤ childCost pchild) (initialCost : ℝ)
    (hCost : childCost pchild ≤ initialCost) (hHcost : (H : ℝ) ≤ Real.exp initialCost) :
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let Qnorm := childCost pchild + (Fintype.card Vars : ℝ) + 2
    let Dnorm := min (d₀ + s * E) ⌊childCost pchild⌋₊
    let normalizedBudget := (Qnorm + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((Dnorm + 1) * (s + 1) ^ Dnorm : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch Vars s d),
      d ≤ Dnorm ∧ d ≤ d₀ + s * E ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := Deck) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - (1 - discount) ^ (stage + 1) * Λ : ℝ) : ℂ))
        initialCost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = fun k => H ≤ A.sides k := by
  classical
  have htarget := recursive_discount_target_mem_Icc hdiscount
    ⟨(Real.exp_pos (-p)).le.trans (ha.trans haΛ), hΛ⟩ stage
  have hreturned := F.returned_fibers_of_productive_padded_relative_induction
    (I := I) (Deck := Deck) (n := n) L hmq B U b hb o S hR hσ ip hip c₀ err hprepare hm hp hσ1 C hC hchart
    N hτhalf hξ1 hsize stride cells center A centerLift productive
    sample read hread hδ hgain hgain1 herr hp0 hDlog hqlog hLlog hNlog hClog hgainlog
    hδearly hPearly hearly ih hp2 hpchild ha haΛ hΛ habsolute hDim H hH hHcut hDpos
    hrest hA hstage f hf hfree hproductive
  have hdec : (fun k : Vars => H.decLe (A.sides k)) =
      (fun k : Vars => Classical.propDecidable (H ≤ A.sides k)) := Subsingleton.elim _ _
  rw [hdec] at hreturned
  exact exists_allocatedFixedCenterNormalizedShearProblem (A := A) (E := Deck)
    s (fun k => H ≤ A.sides k) centerLift hcenter productive hmass hsupported
    sample read hread (childCost pchild) initialCost hchildCost hCost
    (fun i => (Nat.cast_le.mpr (Nat.le_of_lt (Nat.lt_of_not_ge i.property))).trans hHcost)
    (d₀ + s * E) f ((1 - discount) ^ (stage + 1) * Λ) htarget (fun x hx => hf x (by simpa only [mem_integerBox] using hx)) hξ1 hreturned

end Erdos3.PolynomialPatch.LowestLayerModel

end

end OAI
