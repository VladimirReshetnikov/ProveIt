import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartFrozenTerminal
import OAI.Combinatorics.Progressions.Lattices.ResidueBoxSliceSubtypeSites
import OAI.Combinatorics.Progressions.Nilpotent.NativeIntegerChartNiltest

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

structure AllocatedExternalLocalChart (cost : ℝ) where
  path : A.Path
  path_supported : 0 < A.law.weight path
  centerLift : ∀ j, U j
  center_eq : coefficientConstantCenter U center =
    -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
      (constantCoefficientArray U (fun s => centerLift s.1)))
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I E n B → ℤ
  recovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
    centerLift path.1.val path.2.val sample read
  keep : LayerSamplerVariables G I n B → Prop
  fixed : {i // ¬keep i} → ℤ
  fixed_in_box : ∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val
  step : ℕ
  step_pos : 0 < step
  slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) step
  dense : IsDenseCommonStrideBox (fun i : {i // keep i} => A.sides i.val) cost slice.integerPoints

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

abbrev Variables := {i // C.keep i}

noncomputable def integerChart : X ⊕ (Σ j, J j) → MvPolynomial C.Variables ℤ :=
  allocatedFrozenIntegerFullChart B U b o poly hm C.centerLift C.path.1.val C.path.2.val
    C.sample C.keep C.fixed

noncomputable def chartValues (u : C.Variables → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  fun i => MvPolynomial.eval u (C.integerChart i)

noncomputable def parameter (u : C.Variables → ℤ) : LayerSamplerVariables G I n B → ℤ :=
  finiteSplitPoint C.keep u C.fixed

theorem parameter_mem (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.parameter u ∈ integerBox A.sides :=
  allocatedFrozenParameterBox_mem B U b S C.keep C.fixed C.fixed_in_box u hu

noncomputable def physical (u : C.Variables → ℤ) : X → ℤ :=
  jointIntegerPhysicalSite (C.parameter u) (C.path.1.val, C.path.2.val)

noncomputable def site (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) : A.Site :=
  ⟨C.parameter u, C.parameter_mem u hu⟩

@[simp] theorem physical_eq_sampler (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.physical u = A.physical C.path (C.site u hu) := rfl

theorem integerChart_support (i) :
    integerSampledRealChart C.integerChart i ∈
      weightedSupportLE (fun _ : C.Variables => 1) (fullTaggedVariableWeight J i) :=
  allocatedFrozenIntegerFullChart_support B U b o poly hm C.centerLift
    C.path.1.val C.path.2.val C.sample C.keep C.fixed i

theorem integerChart_spatial (u : C.Variables → ℤ) :
    integerSampledSpatial C.integerChart u = C.physical u :=
  allocatedFrozenIntegerFullChart_spatial B U b o poly hm C.centerLift
    C.path.1.val C.path.2.val C.sample C.keep C.fixed u

theorem chartValues_spatial (u : C.Variables → ℤ) (x : X) :
    C.chartValues u (Sum.inl x) = C.physical u x :=
  congrFun (C.integerChart_spatial u) x

theorem slice_parameter_mem (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    C.parameter u ∈ integerBox A.sides :=
  C.parameter_mem u (C.slice.integerPoints_subset_integerBox hu)

theorem slice_index (j : ∀ i, Fin (C.slice.length i)) :
    commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step (C.slice.integerPoint j) =
      fun i => ((j i).val : ℤ) :=
  C.slice.commonStrideIndex_integerPoint C.step_pos j

theorem path_support :
    columnResiduePattern stride C.path.2.val ∈ cells ∧
    0 < allocatedCenteredJointDensity B U b hb o hR hσ S poly hm center C.path.1.val C.path.2.val :=
  A.law_support C.path C.path_supported

end AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (Fmark : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

structure AllocatedExternalLocalCandidate where
  orbit : D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1)
  mark_on_slice : ∀ u ∈ C.slice.integerPoints,
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ : C.Variables => 1) u orbit) =
    Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (C.chartValues u) marked

namespace AllocatedExternalLocalCandidate

variable {C D Fmark φ marked}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

noncomputable def value (u : C.Variables → ℤ) : D.Space :=
  QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
    (fun _ : C.Variables => 1) u candidate.orbit)

noncomputable def score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) : ℝ :=
  (𝔼 u ∈ C.slice.integerPoints, weight (C.physical u) *
    observable (C.physical u) (candidate.value u)).re

theorem mark_integerPoint (j : ∀ i, Fin (C.slice.length i)) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ : C.Variables => 1)
        (C.slice.integerPoint j) candidate.orbit) =
    Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
      (C.chartValues (C.slice.integerPoint j)) marked := by
  apply candidate.mark_on_slice
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.ResidueBoxSlice

variable {I : Type*} [Fintype I] [DecidableEq I] {N : I → ℕ} {q : ℕ}

theorem length_gt_of_dense_exp_side (Q : ResidueBoxSlice N q)
    (hq : 0 < q) {densityCost : ℝ}
    (hdense : IsDenseCommonStrideBox N densityCost Q.integerPoints)
    (degree : ℕ) (i : I)
    (hside : Real.exp densityCost * ((degree + 1 : ℕ) : ℝ) ≤ (N i : ℝ)) :
    degree < Q.length i := by
  have hlength := Q.length_lower_of_dense hq hdense i
  have h := mul_le_mul_of_nonneg_left hside (Real.exp_nonneg (-densityCost))
  have hexp : Real.exp (-densityCost) * Real.exp densityCost = 1 := by
    rw [← Real.exp_add]
    simp
  rw [← mul_assoc, hexp, one_mul] at h
  have hnat : degree + 1 ≤ Q.length i := by exact_mod_cast h.trans hlength
  omega

end Erdos3.ResidueBoxSlice

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem slice_length_gt_of_dense_side
    {densityCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (degree : ℕ)
    (hside : ∀ i : C.Variables,
      Real.exp densityCost * ((degree + 1 : ℕ) : ℝ) ≤ (A.sides i.val : ℝ))
    (i : C.Variables) : degree < C.slice.length i :=
  C.slice.length_gt_of_dense_exp_side C.step_pos hdense degree i (hside i)

theorem slice_length_gt_of_dense_cutoff
    {densityCost cutoff : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : C.Variables => A.sides i.val)
      densityCost C.slice.integerPoints)
    (degree : ℕ)
    (hcutoff : Real.exp densityCost * ((degree + 1 : ℕ) : ℝ) ≤ cutoff)
    (hside : ∀ i, C.keep i → cutoff ≤ layerSamplerBox B U b S i)
    (i : C.Variables) : degree < C.slice.length i := by
  apply C.slice_length_gt_of_dense_side hdense degree _ i
  intro a
  exact (hcutoff.trans (hside a.val a.property)).trans_eq
    (allocatedParameterBox_side_eq B U b S a.val)

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    (D : RationalFilteredNilmanifold L r d) (Fmark : NilpotentLieFiltration M t)
    (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)

structure AllocatedExternalCandidateProblem (cost massThreshold scoreThreshold : ℝ) where
  productive : Finset A.Path
  mass : massThreshold ≤ A.law.mass productive
  chart : ∀ _z : productive, AllocatedExternalLocalChart (E := E) A cost
  chart_path : ∀ z, (chart z).path = z.val
  centerLift : ∀ j, U j
  chart_centerLift : ∀ z, (chart z).centerLift = centerLift
  frozen_side : ∀ z (i : {i // ¬(chart z).keep i}), (A.sides i.val : ℝ) ≤ Real.exp cost
  candidate : ∀ z, AllocatedExternalLocalCandidate (chart z) D Fmark φ marked
  score : ∀ z, scoreThreshold ≤ (candidate z).score observable weight

namespace AllocatedExternalCandidateProblem
variable {A D Fmark φ marked observable weight cost massThreshold scoreThreshold}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

noncomputable def ambientScore
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) : ℝ :=
  (𝔼 u ∈ points, weight ((P.chart z).physical u) *
    observable ((P.chart z).physical u) (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        ((P.chart z).chartValues u) ambient))).re

structure Conclusion (outputCost outputMass outputScore : ℝ) where
  ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)
  marked : map (realLieHomToRat (realificationLieHom φ)).toLinearMap ambient.log = marked.log
  retained : Finset A.Path
  subset : retained ⊆ P.productive
  mass : outputMass ≤ A.law.mass retained
  step : ∀ _z : retained, ℕ
  step_pos : ∀ z, 0 < step z
  slice : ∀ z : retained, ResidueBoxSlice
    (fun i : (P.chart ⟨z.val, subset z.property⟩).Variables => A.sides i.val) (step z)
  dense : ∀ z, IsDenseCommonStrideBox
    (fun i : (P.chart ⟨z.val, subset z.property⟩).Variables => A.sides i.val)
      outputCost (slice z).integerPoints
  inside : ∀ z, (slice z).integerPoints ⊆
    (P.chart ⟨z.val, subset z.property⟩).slice.integerPoints
  score : ∀ z, outputScore ≤ P.ambientScore ambient
    ⟨z.val, subset z.property⟩ (slice z).integerPoints

end AllocatedExternalCandidateProblem

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct

attribute [local irreducible] realChartSubstitute

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (Fmark : NilpotentLieFiltration M t) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

theorem allocatedExternalLocal_mark_of_formal
    (orbit : D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    (hmark : map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) orbit.log =
      realChartSubstitute (integerSampledRealChart C.integerChart) marked.log)
    (u : C.Variables → ℤ) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fun _ : C.Variables => 1) u orbit) =
    Fmark.realification.polynomialOrbitEval (fullTaggedVariableWeight J) (C.chartValues u) marked := by
  rw [← D.filtration.realification.polynomialOrbitRealEval_integer _ orbit u,
    ← Fmark.realification.polynomialOrbitRealEval_integer _ marked (C.chartValues u)]
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom φ (eval₂ (fun i => (u i : ℝ)) orbit.log) =
    eval₂ (fun i => (C.chartValues u i : ℝ)) marked.log
  have heval := congrArg (eval₂ (fun i => (u i : ℝ))) hmark
  refine (eval₂_map (realificationLieHom φ).toLinearMap
    (fun i => (u i : ℝ)) orbit.log).symm.trans (heval.trans ?_)
  refine (eval₂_realChartSubstitute (integerSampledRealChart C.integerChart)
    (fun i => (u i : ℝ)) marked.log).trans ?_
  apply congrArg (fun z => eval₂ z marked.log)
  funext i
  exact integerSampledRealChart_eval C.integerChart u i

def AllocatedExternalLocalCandidate.ofFormalMark
    (orbit : D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    (hmark : map ((realificationLieHom φ).toLinearMap.restrictScalars ℚ) orbit.log =
      realChartSubstitute (integerSampledRealChart C.integerChart) marked.log) :
    AllocatedExternalLocalCandidate C D Fmark φ marked where
  orbit := orbit
  mark_on_slice u _ := allocatedExternalLocal_mark_of_formal C D Fmark φ marked orbit hmark u

end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

theorem polynomialOrbitIntegerChart_eval
    {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))
    (g : F.realification.PolynomialOrbit w) (x : τ → ℤ) :
    F.realification.polynomialOrbitEval v x
      (F.polynomialOrbitRealChart w v (integerSampledRealChart β) hβ g) =
    F.realification.polynomialOrbitEval w (fun i => MvPolynomial.eval x (β i)) g := by
  rw [← F.realification.polynomialOrbitRealEval_integer,
    F.polynomialOrbitRealChart_realEval]
  simp only [integerSampledRealChart_eval]
  rw [F.realification.polynomialOrbitRealEval_integer]

end Erdos3.NilpotentLieFiltration

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {P : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ j, LieRing (P j)] [∀ j, LieAlgebra ℚ (P j)]
    {s d : ℕ} {dp : Pivot → ℕ} (D : RationalFilteredNilmanifold L s d)
    (Fmark : NilpotentLieFiltration M s) (φ : L →ₗ⁅ℚ⁆ M)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

namespace AllocatedExternalLocalCandidate

variable {C D Fmark φ marked}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (partners : ∀ j, RationalFilteredNilmanifold (P j) s (dp j))
    (Q : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

noncomputable def optionJointLocalOrbits : ∀ i : Option Pivot,
    (optionFactors D partners i).filtration.realification.PolynomialOrbit
      (fun _ : C.Variables => 1)
  | none => candidate.orbit
  | some j => (partners j).filtration.polynomialOrbitRealChart
      (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support (Q j)

omit [Fintype Pivot] in
@[simp] theorem optionJointLocalOrbits_none :
    candidate.optionJointLocalOrbits partners Q none = candidate.orbit := rfl

omit [Fintype Pivot] in
@[simp] theorem optionJointLocalOrbits_some (j : Pivot) :
    candidate.optionJointLocalOrbits partners Q (some j) =
      (partners j).filtration.polynomialOrbitRealChart
        (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
        (integerSampledRealChart C.integerChart) C.integerChart_support (Q j) := rfl

noncomputable def optionJointMarkedOrbits : ∀ i : Option Pivot,
    (optionFiltrations Fmark (fun j => (partners j).filtration) i).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)
  | none => marked
  | some j => Q j

noncomputable def optionJoint :
    AllocatedExternalLocalCandidate C (optionProduct D partners)
      (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => (partners j).filtration)))
      (optionMarkedLieMap (L := P) φ)
      (piRealOrbit (optionFiltrations Fmark (fun j => (partners j).filtration))
        (optionJointMarkedOrbits (marked := marked) (partners := partners) Q)) where
  orbit := piRealOrbit (fun i => (optionFactors D partners i).filtration)
    (candidate.optionJointLocalOrbits partners Q)
  mark_on_slice := by
    intro x hx
    apply (realBCHPiEquiv
      (optionFiltrations Fmark (fun j => (partners j).filtration))).injective
    funext i
    cases i with
    | none =>
      rw [realBCHPiEquiv_optionMarkedLieMap_none D.filtration Fmark
        (fun j => (partners j).filtration) φ]
      exact (congrArg
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.lowerCentralSeries_eq_bot) φ)
        (piRealOrbit_eval (fun i => (optionFactors D partners i).filtration)
          (candidate.optionJointLocalOrbits partners Q) x none)).trans
        ((candidate.mark_on_slice x hx).trans
          (piRealOrbit_eval (optionFiltrations Fmark (fun j => (partners j).filtration))
            (optionJointMarkedOrbits (marked := marked) (partners := partners) Q)
            (C.chartValues x) none).symm)
    | some j =>
      rw [realBCHPiEquiv_optionMarkedLieMap_some D.filtration Fmark
        (fun j => (partners j).filtration) φ]
      exact (piRealOrbit_eval (fun i => (optionFactors D partners i).filtration)
        (candidate.optionJointLocalOrbits partners Q) x (some j)).trans
        (((partners j).filtration.polynomialOrbitIntegerChart_eval
          (fullTaggedVariableWeight J) (fun _ : C.Variables => 1)
          C.integerChart C.integerChart_support (Q j) x).trans
          (piRealOrbit_eval (optionFiltrations Fmark (fun j => (partners j).filtration))
            (optionJointMarkedOrbits (marked := marked) (partners := partners) Q)
            (C.chartValues x) (some j)).symm)

@[simp] theorem optionJoint_orbit :
    (candidate.optionJoint partners Q).orbit =
      piRealOrbit (fun i => (optionFactors D partners i).filtration)
        (candidate.optionJointLocalOrbits partners Q) := rfl

@[simp] theorem optionJoint_value_projection (x : C.Variables → ℤ) :
    optionOriginalSpaceProjection D partners ((candidate.optionJoint partners Q).value x) =
      candidate.value x :=
  optionOriginalSpaceProjection_piRealOrbit D partners
    (candidate.optionJointLocalOrbits partners Q) x

@[simp] theorem optionJoint_score (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) :
    (candidate.optionJoint partners Q).score
      (optionOriginalObservable D partners observable) weight =
      candidate.score observable weight := by
  unfold score
  simp only [optionOriginalObservable_apply, optionJoint_value_projection]

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (Fnew : NilpotentLieFiltration M t) (hFnew : Fnew = Fmark)

noncomputable def changeTargetFiltration :
    AllocatedExternalLocalCandidate C D Fnew φ
      (Fmark.realPolynomialOrbitChangeFiltration Fnew hFnew
        (fullTaggedVariableWeight (X := X) J) marked) where
  orbit := candidate.orbit
  mark_on_slice u hu := by
    rw [Fmark.realPolynomialOrbitChangeFiltration_eval Fnew hFnew]
    exact candidate.mark_on_slice u hu

@[simp] theorem changeTargetFiltration_orbit :
    (candidate.changeTargetFiltration Fnew hFnew).orbit = candidate.orbit := rfl

@[simp] theorem changeTargetFiltration_value (u : C.Variables → ℤ) :
    (candidate.changeTargetFiltration Fnew hFnew).value u = candidate.value u := rfl

@[simp] theorem changeTargetFiltration_score
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ) :
    (candidate.changeTargetFiltration Fnew hFnew).score observable weight =
      candidate.score observable weight := rfl

end AllocatedExternalLocalCandidate
end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {Pivot : Type v} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    {s d : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold LG s d}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (partners : ∀ j, RationalFilteredNilmanifold (MG j) s (dp j))
    (Q : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

def optionJoint :
    AllocatedExternalCandidateProblem (E := E) A (optionProduct D partners)
      (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => (partners j).filtration)))
      (optionMarkedLieMap (L := MG) φ)
      (piRealOrbit (optionFiltrations Fmark (fun j => (partners j).filtration))
        (AllocatedExternalLocalCandidate.optionJointMarkedOrbits
          (marked := marked) (partners := partners) Q))
      (optionOriginalObservable D partners observable) weight cost massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart := P.chart
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side := P.frozen_side
  candidate z := (P.candidate z).optionJoint partners Q
  score z := by
    rw [AllocatedExternalLocalCandidate.optionJoint_score]
    exact P.score z

@[simp] theorem optionJoint_productive : (P.optionJoint partners Q).productive = P.productive := rfl

@[simp] theorem optionJoint_chart (z : P.productive) :
    (P.optionJoint partners Q).chart z = P.chart z := rfl

@[simp] theorem optionJoint_candidate_orbit (z : P.productive) :
    ((P.optionJoint partners Q).candidate z).orbit =
      piRealOrbit (fun i => (optionFactors D partners i).filtration)
        ((P.candidate z).optionJointLocalOrbits partners Q) := rfl

def onPaths (paths : Finset A.Path) (hsub : paths ⊆ P.productive)
    {newMass : ℝ} (hmass : newMass ≤ A.law.mass paths) :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost newMass scoreThreshold where
  productive := paths
  mass := hmass
  chart z := P.chart ⟨z.val, hsub z.property⟩
  chart_path z := P.chart_path ⟨z.val, hsub z.property⟩
  centerLift := P.centerLift
  chart_centerLift z := P.chart_centerLift ⟨z.val, hsub z.property⟩
  frozen_side z := P.frozen_side ⟨z.val, hsub z.property⟩
  candidate z := P.candidate ⟨z.val, hsub z.property⟩
  score z := P.score ⟨z.val, hsub z.property⟩

@[simp] theorem onPaths_productive (paths : Finset A.Path) (hsub : paths ⊆ P.productive)
    {newMass : ℝ} (hmass : newMass ≤ A.law.mass paths) :
    (P.onPaths paths hsub hmass).productive = paths := rfl

def conclusion_of_onPaths (paths : Finset A.Path) (hsub : paths ⊆ P.productive)
    {newMass : ℝ} (hmass : newMass ≤ A.law.mass paths)
    {outCost outMass outScore : ℝ}
    (result : (P.onPaths paths hsub hmass).Conclusion outCost outMass outScore) :
    P.Conclusion outCost outMass outScore where
  ambient := result.ambient
  marked := result.marked
  retained := result.retained
  subset := fun _ ha => hsub (result.subset ha)
  mass := result.mass
  step := result.step
  step_pos := result.step_pos
  slice := result.slice
  dense := result.dense
  inside := result.inside
  score := result.score

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

section

universe u v

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {Pivot : Type v} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    {s d : ℕ} {dp : Pivot → ℕ} {D : RationalFilteredNilmanifold LG s d}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (partners : ∀ j, RationalFilteredNilmanifold (MG j) s (dp j))
    (Q : ∀ j, (partners j).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

@[simp] theorem optionJoint_ambientScore
    (ambient : (optionProduct D partners).filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ)) :
    (P.optionJoint partners Q).ambientScore ambient z points =
      P.ambientScore (optionOriginalOrbit D partners ambient) z points := by
  unfold ambientScore
  exact congrArg Complex.re (optionOriginalOrbit_score D partners ambient observable
    points (P.chart z).physical (P.chart z).chartValues (fun u => weight ((P.chart z).physical u)))

def conclusion_of_optionJoint {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore) :
    P.Conclusion outputCost outputMass outputScore where
  ambient := optionOriginalOrbit D partners result.ambient
  marked := optionOriginalOrbit_mark_log D partners Fmark φ result.ambient
    (AllocatedExternalLocalCandidate.optionJointMarkedOrbits
      (marked := marked) (partners := partners) Q) result.marked
  retained := result.retained
  subset := result.subset
  mass := result.mass
  step := result.step
  step_pos := result.step_pos
  slice := result.slice
  dense := result.dense
  inside := result.inside
  score z := (result.score z).trans_eq
    (P.optionJoint_ambientScore partners Q result.ambient _ _)

@[simp] theorem conclusion_of_optionJoint_ambient {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_optionJoint partners Q result).ambient =
      optionOriginalOrbit D partners result.ambient := rfl

@[simp] theorem conclusion_of_optionJoint_retained {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore) :
    (P.conclusion_of_optionJoint partners Q result).retained = result.retained := rfl

@[simp] theorem conclusion_of_optionJoint_step {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore)
    (z : result.retained) :
    (P.conclusion_of_optionJoint partners Q result).step z = result.step z := rfl

@[simp] theorem conclusion_of_optionJoint_slice {outputCost outputMass outputScore : ℝ}
    (result : (P.optionJoint partners Q).Conclusion outputCost outputMass outputScore)
    (z : result.retained) :
    (P.conclusion_of_optionJoint partners Q result).slice z = result.slice z := rfl

end AllocatedExternalCandidateProblem

end

end Erdos3.VectorPolynomial

end

end OAI
