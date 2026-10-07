import OAI.Combinatorics.Progressions.Estimates.AllocatedFrozenTaggedTwistStepDrop
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSymbolBasisIndependence

namespace OAI

universe u

section

namespace Erdos3
open Module RationalFilteredNilmanifold BooleanCubeKernel
open VectorPolynomial
open scoped TensorProduct BigOperators NNReal

theorem exists_native_twist_variation_slice_fixed_basis_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (c : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ν : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hC : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (c '' {i | k ≤ ν i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (c i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (c.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
        ∀ {K : Type*}
      [Fintype K] [DecidableEq K] [Nonempty K]
      {P : K → ℕ} {q : ℕ} (S : ResidueBoxSlice P q) (_hq : 0 < q)
      (hlen : ∀ k, 0 < S.length k) {p : ℝ} (_hp : 0 ≤ p)
      (_hS : ∀ k, Real.exp (-p) * (P k : ℝ) ≤ S.length k)
      (_hP : ∀ k, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P k : ℝ))
      {M : ℕ} (_hM : 0 < M) (_hperiod : (M : ℝ) ≤ Real.exp p)
      (twist : integerBox P → ℂ) (_htwist : ∀ t, ‖twist t‖ ≤ 1)
      {variation : ℝ} (_hvariation_nonneg : 0 ≤ variation)
      (_hvariation_bound : variation ≤ Real.exp p)
      (_hvariation : ∀ u v : integerBox P,
        (∀ k, (u.val k : ZMod M) = (v.val k : ZMod M)) →
        ∀ δ : ℝ, 0 ≤ δ →
        (∀ k, |(u.val k : ℝ) / P k - (v.val k : ℝ) / P k| ≤ δ) →
        ‖twist u - twist v‖ ≤ variation * δ)
      (V : D.Niltest (fun _ : K => 1)) (W : E.Niltest (fun _ : K => 1))
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
      (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (_hK : (Fintype.card K : ℝ) ≤ p)
      (_hbias : Real.exp (-p) ≤ ‖(S.fullSliceLaw hlen).complexMean (fun t =>
        star (twist t) *
          (V.eval t.val * W.eval t.val))‖),
      (pi (pairModels D E)).filtration.ControlledSymbolFactorization c ν hC
        (pairFrequency η θ) (fun k => (P k : ℝ))
        (pairOrbitSymbol D E V.orbit W.orbit c ν hC)
        ((fixedAdaptedSymbolTransferInput pGeo
          (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_twist_variation_slice_step_drop s hs
  obtain ⟨A, hA, hfixed⟩ := exists_fixed_adapted_symbol_factorization_basis s
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨c, ν, N, hc, _, _, hforward, hinverse, _, _, _, _, _, htransfer⟩ :=
    hfixed (pi (pairModels D E)) hpGeo hGeo
  refine ⟨c, ν, hc, hforward, hinverse, ?_⟩
  intro K _ _ _ P q S hq hlen p hp hS hP M hM hperiod twist htwist
    variation hvariation_nonneg hvariation_bound hvariation
    V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  obtain ⟨b, ω, hF, hb, hfactor⟩ := hstep S hq hlen hp hS hP hM hperiod
    twist htwist hvariation_nonneg hvariation_bound hvariation
    D E V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  let cost := (p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23)
  have hcost : 0 ≤ cost := by dsimp only [cost]; positivity
  have hPpos (k : K) : (0 : ℝ) < P k := (Real.exp_pos _).trans_le (hP k)
  have hqGeo : pGeo ≤ pGeo + p + cost := by linarith
  have hqP : p ≤ pGeo + p + cost := by linarith
  have hqCost : cost ≤ pGeo + p + cost := by linarith
  have hbase : (p + 2 + C) ^ C ≤ cost := by
    dsimp only [cost]
    linarith [show 0 ≤ (s : ℝ) * (9 * p + 23) by positivity]
  have htransferred := htransfer hqGeo (hK.trans hqP) b ω hF
    (fun i j => (hb i j).trans (hbase.trans hqCost)) (fun k => (P k : ℝ)) hPpos
    (pairFrequency η θ) (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
    (hfactor.mono (pi (pairModels D E)).filtration b ω hF hqCost hPpos)
  rw [pairOrbitSymbol_basis_independent D E V.orbit W.orbit b ω hF c ν hc] at htransferred
  exact htransferred

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

theorem exists_allocated_frozen_tagged_twist_fixed_basis_step_drop
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ C A : ℕ, 2 ≤ C ∧ 2 ≤ A ∧ ∀
      {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG] [LieRing MG] [LieAlgebra ℚ MG]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
      [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
      (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
      {pGeo : ℝ} (_hpGeo : 0 ≤ pGeo)
      (_hGeo : (pi (pairModels D E)).GeometryComplexityLE pGeo),
      ∃ (bFixed : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ωFixed : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hFixed : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (bFixed '' {i | k ≤ ωFixed i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (bFixed i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (bFixed.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I Deck J : Fin m → Type*}
      [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
      (hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
      (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
      {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag R σ)
      (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hm : ∀ j d, coefficients (poly j) d ∈ U j)
      (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
      (c : ∀ j, U j) (a : X → ℤ) (N : X → ℕ) (_hN : ∀ x, 0 < N x)
      {τ ξ : ℝ} (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hξ : ξ ≤ 1)
      (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
      (_hv : v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1)
      (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
      (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ)
      (_hread : AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag o S hR hσ poly hm c a v sample read)
      (_hσ1 : ∀ j, σ j ≤ 1) (Cgeo : Fin m → ℝ) (_hCgeo : ∀ j, 0 ≤ Cgeo j)
      (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
      (_hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
      {periodCap coverCap : ℝ} {L : ℝ≥0}
      (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
      {p : ℝ} (_hp : 0 ≤ p)
      (_hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
      (_hvariationBound : (L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
        ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
      (keep : LayerSamplerVariables G I n B → Prop) [Nonempty {i // keep i}]
      (fixed : {i // ¬keep i} → ℤ)
      (_hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val),
      let P := fun i : {i // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U btag S) i.val
      let β := allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed
      ∀ {q : ℕ} (Q : ResidueBoxSlice P q) (_hq : 0 < q)
        (hlen : ∀ i, 0 < Q.length i)
        (_hQ : ∀ i, Real.exp (-p) * (P i : ℝ) ≤ Q.length i)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (P i : ℝ))
        (V : D.Niltest (fun _ : {i // keep i} => 1))
        (W : E.Niltest (fun _ : {i // keep i} => 1))
        (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p) (_hWnorm : W.normBound ≤ 1)
        (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
        (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
        (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
        (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          V.observable (z • x) = CircleFourier.character
            ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
        (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
          W.observable (z • x) = CircleFourier.character
            ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
        (_hK : (Fintype.card {i // keep i} : ℝ) ≤ p)
        (_hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
          star (twist.eval N poly (integerSampledSpatial β t.val)) *
            (V.eval t.val * W.eval t.val))‖),
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization bFixed ωFixed hFixed
          (pairFrequency η θ) (fun k => (P k : ℝ))
          (pairOrbitSymbol D E V.orbit W.orbit bFixed ωFixed hFixed)
          ((fixedAdaptedSymbolTransferInput pGeo
            (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, A, hC, hA, hstep⟩ :=
    exists_native_twist_variation_slice_fixed_basis_step_drop s hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨bFixed, ωFixed, hFixed, hforward, hinverse, hlocal⟩ := hstep D E hpGeo hGeo
  refine ⟨bFixed, ωFixed, hFixed, hforward, hinverse, ?_⟩
  intro m G X _ _ I Deck J _ _ n B _ U btag hbtag o R σ S hR hσ poly hm hpoly
    c a N hN τ ξ hτ hτ1 hξ v hv sample read hread hσ1 Cgeo hCgeo hchart hsmall
    periodCap coverCap L twist p hp hperiod hvariationBound keep _ fixed hfixed
  dsimp only
  intro q Q hq hlen hQ hP V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  have hsmallOne : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 :=
    fun j => (hsmall j).trans (by norm_num)
  apply hlocal Q hq hlen hp hQ hP (mul_pos twist.modulus_pos twist.cover_pos)
    hperiod (fun t => twist.eval N poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B U btag o poly hm c a v sample keep fixed) t.val))
    (fun _ => twist.norm_eval_le N poly _)
    (by positivity) hvariationBound ?_
    V W hV hW hWnorm η θ hηheight hθheight hη hθ hK hbias
  intro x y hres δ hδ hcell
  exact hread.frozen_twist_variation B U btag hbtag o S hR hσ poly hm hpoly
    c a N hN hτ hτ1 hξ v hv sample read hσ1 Cgeo hCgeo hchart hsmallOne
    twist keep fixed hfixed x y hres hδ hcell

end Erdos3.VectorPolynomial

end

end OAI
