import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartKeepBounds
import OAI.Combinatorics.Progressions.Geometry.NativeChartPairSymbolCompatibility
import OAI.Combinatorics.Progressions.Linear.AllocatedFrozenTaggedTwistFixedBasisStepDrop
import OAI.Combinatorics.Progressions.Linear.ControlledProjectionUniformBudget
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw

namespace OAI

universe u

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {X : Type*} [Fintype X] [DecidableEq X] {N : X → ℕ} {q : ℕ}

noncomputable def fullSlicePoints (S : ResidueBoxSlice N q) : Finset (integerBox N) :=
  Finset.univ.image S.fullSlicePointInIntegerBox

theorem fullSlicePointInIntegerBox_injective (S : ResidueBoxSlice N q) (hq : 0 < q) :
    Function.Injective S.fullSlicePointInIntegerBox := by
  intro u v h
  exact S.integerPoint_injective hq (congrArg Subtype.val h)

theorem fullSlicePoints_image_val (S : ResidueBoxSlice N q) :
    S.fullSlicePoints.image Subtype.val = S.integerPoints := by
  simp only [fullSlicePoints, integerPoints, Finset.image_image]
  rfl

theorem fullSlicePoints_nonempty (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) : S.fullSlicePoints.Nonempty := by
  let u : ∀ i, Fin (S.length i) := fun i => ⟨0, hlen i⟩
  exact ⟨S.fullSlicePointInIntegerBox u, Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩⟩

theorem expect_fullSlicePoints (S : ResidueBoxSlice N q) (hq : 0 < q)
    {V : Type*} [AddCommMonoid V] [Module ℚ≥0 V] (f : integerBox N → V) :
    (𝔼 x ∈ S.fullSlicePoints, f x) = 𝔼 u, f (S.fullSlicePointInIntegerBox u) :=
  Finset.expect_image (S.fullSlicePointInIntegerBox_injective hq).injOn

theorem fullSliceLaw_complexMean_eq_expect_points (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (hq : 0 < q) (f : integerBox N → ℂ) :
    (S.fullSliceLaw hlen).complexMean f = 𝔼 x ∈ S.fullSlicePoints, f x := by
  rw [S.fullSliceLaw_complexMean hlen]
  exact (S.expect_fullSlicePoints hq f).symm

theorem fullSliceLaw_mean_eq_expect_points (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (hq : 0 < q) (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f = 𝔼 x ∈ S.fullSlicePoints, f x := by
  rw [S.fullSliceLaw_mean hlen]
  exact (S.expect_fullSlicePoints hq f).symm

end Erdos3.ResidueBoxSlice

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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem low_residual
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (k : ℕ) (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val))
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (C.physical u x : ℝ)) (lowTaggedPolynomial J k poly i) -
      (C.centerLift (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k C.integerChart u i : ℝ)| ≤ 1 / 8 := by
  rw [← C.integerChart_spatial]
  exact C.recovered.integerFrozenFullChart_low_residual B U b hb o S hR hσ poly hm
    hσ1 H hH hchart hsmall hp C.centerLift C.path.1.val C.path.2.val C.sample C.read
    C.keep C.fixed C.fixed_in_box k u hu i

theorem low_residual_on_slice
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (k : ℕ) (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (C.physical u x : ℝ)) (lowTaggedPolynomial J k poly i) -
      (C.centerLift (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k C.integerChart u i : ℝ)| ≤ 1 / 8 :=
  C.low_residual hσ1 H hH hchart hsmall hp k u
    (C.slice.integerPoints_subset_integerBox hu) i

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable def fullTaggedPhysicalIntegerPoint {m : ℕ} {X : Type*}
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) : X ⊕ (Σ j, J j) → ℤ :=
  Sum.elim x (fun a => round (eval (fun i => (x i : ℝ)) (poly a.1) a.2 - c a.1 a.2))

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

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem chartValues_tag_eq_round (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val))
    (j : Fin m) (i : J j) :
    C.chartValues u (Sum.inr ⟨j, i⟩) =
      round (eval (fun x => (C.physical u x : ℝ)) (poly j) i - (C.centerLift j).val i) := by
  have hj : j.val + 1 ≤ m + 1 := by omega
  have hr := C.low_residual hσ1 H hH hchart hsmall hp (m + 1) u hu
    (lowTaggedSlot J (m + 1) j hj i)
  rw [lowTaggedPolynomial_eval] at hr
  simp only [integerSampledLowTags] at hr
  rw [lowTaggedIndex_slot] at hr
  change |eval (fun x => (C.physical u x : ℝ)) (poly j) i - (C.centerLift j).val i -
    (C.chartValues u (Sum.inr ⟨j, i⟩) : ℝ)| ≤ 1 / 8 at hr
  symm
  apply round_eq_iff.mpr
  have hb := abs_le.mp hr
  constructor <;> linarith

theorem chartValues_eq_physicalIntegerPoint (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (C.centerLift j).val) (C.physical u) := by
  funext a
  rcases a with x | ⟨j, i⟩
  · exact C.chartValues_spatial u x
  · exact C.chartValues_tag_eq_round hσ1 H hH hchart hsmall hp u hu j i

theorem chartValues_eq_physicalIntegerPoint_on_slice (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (C.centerLift j).val) (C.physical u) :=
  C.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp u
    (C.slice.integerPoints_subset_integerBox hu)

theorem chartValues_eq_physicalIntegerPoint_of_center
    (c : ∀ j, U j) (hc : C.centerLift = c) (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) :
    C.chartValues u = fullTaggedPhysicalIntegerPoint J poly
      (fun j => (c j).val) (C.physical u) := by
  rw [← hc]
  exact C.chartValues_eq_physicalIntegerPoint_on_slice hσ1 H hH hchart hsmall hp u hu

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

variable {X : Type*} {J : Fin 0 → Type*}

def zeroLayerPhysicalPoint (x : X → ℤ) : X ⊕ Sigma J → ℤ :=
  Sum.elim x (fun a => Fin.elim0 a.1)

theorem fullTaggedPhysicalIntegerPoint_zero_layers
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℤ) :
    fullTaggedPhysicalIntegerPoint J poly c x = zeroLayerPhysicalPoint x := by
  funext v
  rcases v with x | a
  · rfl
  · exact Fin.elim0 a.1

noncomputable def zeroLayerSpatialChart : X ⊕ Sigma J → MvPolynomial X ℝ :=
  Sum.elim MvPolynomial.X (fun a => Fin.elim0 a.1)

theorem zeroLayerSpatialChart_support (v : X ⊕ Sigma J) :
    zeroLayerSpatialChart v ∈ weightedSupportLE (fun _ : X => 1)
      (fullTaggedVariableWeight J v) := by
  rcases v with x | a
  · exact weightedSupportLE_X (fun _ : X => 1) x
  · exact Fin.elim0 a.1

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (A : PolynomialPatch V s d)

noncomputable def ofZeroLayerShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) : PolynomialPatch X s d :=
  A.ofWeightedChartShearOrbit (fullTaggedVariableWeight J)
    zeroLayerSpatialChart zeroLayerSpatialChart_support g

@[simp] theorem ofZeroLayerShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofZeroLayerShearOrbit g).kernel = A.kernel := rfl

@[simp] theorem ofZeroLayerShearOrbit_complexity
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    relativePatchComplexity (A.ofZeroLayerShearOrbit g) = relativePatchComplexity A := rfl

theorem ofZeroLayerShearOrbit_value_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) (x : X → ℤ) :
    (A.ofZeroLayerShearOrbit g).value (fun i => (x i : ℝ)) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (zeroLayerPhysicalPoint x) g)) := by
  rw [ofZeroLayerShearOrbit, ofWeightedChartShearOrbit_value]
  have hpoint : (fun i => MvPolynomial.eval (fun k => (x k : ℝ)) (zeroLayerSpatialChart i)) =
      fun i => (zeroLayerPhysicalPoint (J := J) x i : ℝ) := by
    funext v
    rcases v with k | a
    · simp only [zeroLayerSpatialChart, Sum.elim_inl, MvPolynomial.eval_X,
        zeroLayerPhysicalPoint]
    · exact Fin.elim0 a.1
  rw [hpoint, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

variable [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem exists_zeroLayer_physical_niltest
    (M : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    {p : ℝ} (hcomplex : (A.shearNiltest M hA).ComplexityLE p)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : X => 1),
      T.observable = (A.shearNiltest M hA).observable ∧
      T.UnitIntervalValued ∧ T.ComplexityLE p ∧
      ∀ x : X → ℤ, T.eval x = ((A.ofZeroLayerShearOrbit g).value
        (fun i => (x i : ℝ)) : ℂ) := by
  obtain ⟨T, hobs, _, _, hunit, hcomp, hval⟩ := A.exists_ordinary_niltest_of_weighted_chart
    M hA hcomplex (fullTaggedVariableWeight J) zeroLayerSpatialChart
    zeroLayerSpatialChart_support g
  exact ⟨T, hobs, hunit, hcomp, hval⟩

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial RationalFilteredNilmanifold
open scoped BigOperators NNReal Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
  {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]

structure AllocatedFrozenTaggedContext where
  U : ∀ j, Submodule ℝ (J j → ℝ)
  btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ
  hbtag : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))
  o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))
  R : Fin m → ℝ
  σ : Fin m → ℝ
  S : LayerSamplerScale (G := G) B U btag R σ
  hR : ∀ j, 0 < R j
  hσ : ∀ j, 0 < σ j
  poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)
  hm : ∀ j d, coefficients (poly j) d ∈ U j
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  N : X → ℕ
  hN : ∀ x, 0 < N x
  τ : ℝ
  ξ : ℝ
  hτ : 0 < τ
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  periodCap : ℝ
  coverCap : ℝ
  L : ℝ≥0

variable {B}

def AllocatedFrozenTaggedContext.sides
    (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
    (keep : LayerSamplerVariables G I n B → Prop) : {i // keep i} → ℕ :=
  fun i => Sum.elim (fun _ : G => Γ.S.value)
    (allocatedPrincipalSides B Γ.U Γ.btag Γ.S) i.val

variable {LG MG : Type u} [LieRing LG] [LieAlgebra ℚ LG]
  [LieRing MG] [LieAlgebra ℚ MG] {s d e : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
  [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]

structure AllocatedFrozenTaggedPairInput
    (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
    (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
    (D : RationalFilteredNilmanifold LG s d) (E : RationalFilteredNilmanifold MG s e)
    (p : ℝ) where
  twist : NormalizedPolynomialTwist X (Σ j, J j) Γ.periodCap Γ.coverCap Γ.L
  c : ∀ j, Γ.U j
  a : X → ℤ
  v : Option (LayerSamplerVariables G I n B) × X → ℤ
  hv : v ∈ rectangularWeightIndices 0
    (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B Γ.U Γ.btag Γ.S (fun _ => 0))
      Γ.τ Γ.ξ Γ.N) 1
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ
  hread : AllocatedCenteredFramedRecoveredSampleAt B Γ.U Γ.btag Γ.hbtag Γ.o Γ.S
    Γ.hR Γ.hσ Γ.poly Γ.hm c a v sample read
  fixed : {i // ¬keep i} → ℤ
  hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i <
    Sum.elim (fun _ : G => Γ.S.value) (allocatedPrincipalSides B Γ.U Γ.btag Γ.S) i.val
  q : ℕ
  Q : ResidueBoxSlice (Γ.sides keep) q
  hq : 0 < q
  hlen : ∀ i, 0 < Q.length i
  hQ : ∀ i, Real.exp (-p) * (Γ.sides keep i : ℝ) ≤ Q.length i
  V : D.Niltest (fun _ : {i // keep i} => 1)
  W : E.Niltest (fun _ : {i // keep i} => 1)
  hp : 0 ≤ p
  hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p
  hvariationBound : (Γ.L : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : V.ComplexityLE p
  hW : W.ComplexityLE p
  hWnorm : W.normBound ≤ 1
  η : LG →ₗ[ℚ] ℚ
  θ : MG →ₗ[ℚ] ℚ
  hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p
  hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p
  hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    V.observable (z • x) = CircleFourier.character
      ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x
  hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
    W.observable (z • x) = CircleFourier.character
      ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p
  hbias : Real.exp (-p) ≤ ‖(Q.fullSliceLaw hlen).complexMean (fun t =>
    star (twist.eval Γ.N Γ.poly (integerSampledSpatial
      (allocatedFrozenIntegerFullChart B Γ.U Γ.btag Γ.o Γ.poly Γ.hm c a v sample keep fixed)
      t.val)) * (V.eval t.val * W.eval t.val))‖

theorem exists_allocatedFrozenTaggedPairInput_fixed_basis_step_drop
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
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra LG MG))) ℚ (PairAlgebra LG MG))
        (ω : Fin (finrank ℚ (PairAlgebra LG MG)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ pGeo + 1) ∧
        (∀ i j, rationalLogHeight (b.repr ((pi (pairModels D E)).basis i) j) ≤ (pGeo + 3) ^ 5) ∧
      ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
        {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
        {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
        (Γ : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B)
        (Deck : Fin m → Type*) (keep : LayerSamplerVariables G I n B → Prop)
        [Nonempty {i // keep i}] {p : ℝ}
        (input : AllocatedFrozenTaggedPairInput Γ Deck keep D E p)
        (_hP : ∀ i, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (Γ.sides keep i : ℝ)),
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency input.η input.θ) (fun k => (Γ.sides keep k : ℝ))
          (pairOrbitSymbol D E input.V.orbit input.W.orbit b ω hF)
          ((fixedAdaptedSymbolTransferInput pGeo
            (pGeo + p + ((p + 2 + C) ^ C + (s : ℝ) * (9 * p + 23))) + A) ^ A) := by
  obtain ⟨C, A, hC, hA, hstep⟩ :=
    exists_allocated_frozen_tagged_twist_fixed_basis_step_drop s hs
  refine ⟨C, A, hC, hA, ?_⟩
  intro LG MG _ _ _ _ d e _ _ _ _ _ _ _ _ D E pGeo hpGeo hGeo
  obtain ⟨b, ω, hF, hforward, hinverse, hlocal⟩ := hstep D E hpGeo hGeo
  refine ⟨b, ω, hF, hforward, hinverse, ?_⟩
  intro m G X _ _ I J _ _ n B _ Γ Deck keep _ p input hP
  exact hlocal B Γ.U Γ.btag Γ.hbtag Γ.o Γ.S Γ.hR Γ.hσ Γ.poly Γ.hm Γ.hpoly
    input.c input.a Γ.N Γ.hN Γ.hτ Γ.hτ1 Γ.hξ input.v input.hv input.sample
    input.read input.hread Γ.hσ1 Γ.Cgeo Γ.hCgeo Γ.hchart Γ.hsmall input.twist
    input.hp input.hperiod input.hvariationBound keep input.fixed input.hfixed
    input.Q input.hq input.hlen input.hQ hP input.V input.W input.hV input.hW
    input.hWnorm input.η input.θ input.hηheight input.hθheight input.hη input.hθ
    input.hK input.hbias

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def frozenTaggedContext
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (periodCap coverCap : ℝ) (Lip : ℝ≥0) :
    AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B where
  U := U
  btag := b
  hbtag := hb
  o := o
  R := R
  σ := σ
  S := S
  hR := hR
  hσ := hσ
  poly := poly
  hm := hm
  hpoly := hpoly
  N := N
  hN := A.size_pos
  τ := τ
  ξ := ξ
  hτ := A.trim_pos
  hτ1 := hτ1
  hξ := hξ
  hσ1 := hσ1
  Cgeo := Cgeo
  hCgeo := hCgeo
  hchart := hchart
  hsmall := hsmall
  periodCap := periodCap
  coverCap := coverCap
  L := Lip

end AllocatedExternalCandidateSampler

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}

local notation "Γ" => A.frozenTaggedContext hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  periodCap coverCap Lip

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)

theorem localLaw_complexMean_eq_fullSliceLaw
    (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
    C.localLaw.complexMean (fun site => f site.val) =
      (C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean
        (fun t => f (C.parameter t.val)) := by
  rw [C.localLaw_complexMean_parameter,
    C.slice.fullSliceLaw_complexMean_eq_expect_points _ C.step_pos,
    ← C.slice.fullSlicePoints_image_val]
  exact Finset.expect_image Subtype.val_injective.injOn

end AllocatedExternalLocalChart

namespace AllocatedFrozenTaggedPairInput

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := Deck) A cost)
    {LG MG LM : Type u} [LieRing LG] [LieAlgebra ℚ LG]
    [LieRing MG] [LieAlgebra ℚ MG] [LieRing LM] [LieAlgebra ℚ LM]
    {s d e t : ℕ} {D : RationalFilteredNilmanifold LG s d}
    {E : RationalFilteredNilmanifold MG s e} {Fmark : NilpotentLieFiltration LM t}
    {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [TopologicalSpace (ℝ ⊗[ℚ] MG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] MG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] MG)] [T2Space (ℝ ⊗[ℚ] MG)]
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (reference : D.Niltest (fullTaggedVariableWeight (X := X) J))
    (partner : E.Niltest (fullTaggedVariableWeight (X := X) J))
    (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    {p : ℝ} (hp : 0 ≤ p) (hcost : cost ≤ p)
    (hperiod : ((twist.modulus * twist.cover : ℕ) : ℝ) ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hV : reference.ComplexityLE p) (hW : partner.ComplexityLE p)
    (hWnorm : partner.normBound ≤ 1)
    (η : LG →ₗ[ℚ] ℚ) (θ : MG →ₗ[ℚ] ℚ)
    (hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
    (hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
    (hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
      reference.observable (z • x) = CircleFourier.character
        ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * reference.observable x)
    (hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
      partner.observable (z • x) = CircleFourier.character
        ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * partner.observable x)
    (hK : (Fintype.card C.Variables : ℝ) ≤ p)

def ofCandidate
    (hcorr : Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (C.physical t.val)) *
          (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p where
  twist := twist
  c := C.centerLift
  a := C.path.1.val
  v := C.path.2.val
  hv := by
    change C.path.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using C.path.2.property
  sample := C.sample
  read := C.read
  hread := C.recovered
  fixed := C.fixed
  hfixed := C.fixed_in_box
  q := C.step
  Q := C.slice
  hq := C.step_pos
  hlen := C.slice.length_pos_of_dense C.dense
  hQ := fun i =>
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost))
      (Nat.cast_nonneg (A.sides i.val))).trans
        (C.slice.length_lower_of_dense C.step_pos C.dense i)
  V := reference.withOrbit candidate.orbit
  W := partner.integerChartPullback (fun _ : C.Variables => 1) C.integerChart C.integerChart_support
  hp := hp
  hperiod := hperiod
  hvariationBound := hvariation
  hV := hV
  hW := hW
  hWnorm := hWnorm
  η := η
  θ := θ
  hηheight := hηheight
  hθheight := hθheight
  hη := hη
  hθ := hθ
  hK := hK
  hbias := by
    change Real.exp (-p) ≤
      ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
        star (twist.eval N poly (integerSampledSpatial C.integerChart t.val)) *
          ((reference.withOrbit candidate.orbit).eval t.val *
            (partner.integerChartPullback (fun _ : C.Variables => 1)
              C.integerChart C.integerChart_support).eval t.val))‖
    simp only [C.integerChart_spatial, Niltest.integerChartPullback_eval,
      Niltest.withOrbit_eval]
    exact hcorr

variable (hcorr : Real.exp (-p) ≤
  ‖(C.slice.fullSliceLaw (C.slice.length_pos_of_dense C.dense)).complexMean (fun t =>
    star (twist.eval N poly (C.physical t.val)) *
      (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val)))‖)

local notation "candidateInput" => ofCandidate A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall
  C candidate reference partner twist hp hcost hperiod hvariation hV hW hWnorm
  η θ hηheight hθheight hη hθ hK hcorr

@[simp] theorem ofCandidate_V_orbit :
    (candidateInput).V.orbit = candidate.orbit := rfl

@[simp] theorem ofCandidate_W_orbit :
    (candidateInput).W.orbit =
      (partner.integerChartPullback (fun _ : C.Variables => 1)
        C.integerChart C.integerChart_support).orbit := rfl

def ofCandidate_of_localLaw
    (hcorr : Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
      star (twist.eval N poly (A.physical C.path site)) *
        (reference.observable (candidate.value (C.retainedParameter site.val)) *
          partner.eval (fullTaggedPhysicalIntegerPoint J poly
            (fun j => (C.centerLift j).val) (A.physical C.path site))))‖) :
    AllocatedFrozenTaggedPairInput Γ Deck C.keep D E p := by
  apply ofCandidate A hpoly hτ1 hξ hσ1 Cgeo hCgeo hchart hsmall C candidate
    reference partner twist hp hcost hperiod hvariation hV hW hWnorm
    η θ hηheight hθheight hη hθ hK
  have he := C.localLaw_complexMean_eq_fullSliceLaw (fun x =>
    star (twist.eval N poly (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter x)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite x (C.path.1.val, C.path.2.val)))))
  change Real.exp (-p) ≤ ‖C.localLaw.complexMean (fun site =>
    star (twist.eval N poly (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val))) *
      (reference.observable (candidate.value (C.retainedParameter site.val)) *
        partner.eval (fullTaggedPhysicalIntegerPoint J poly
          (fun j => (C.centerLift j).val)
          (jointIntegerPhysicalSite site.val (C.path.1.val, C.path.2.val)))))‖ at hcorr
  rw [he] at hcorr
  have hf : (fun t : integerBox (fun i : C.Variables => A.sides i.val) =>
      star (twist.eval N poly (C.physical t.val)) *
        (reference.observable (candidate.value t.val) * partner.eval (C.chartValues t.val))) =
      (fun t => star (twist.eval N poly
        (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))) *
          (reference.observable (candidate.value (C.retainedParameter (C.parameter t.val))) *
            partner.eval (fullTaggedPhysicalIntegerPoint J poly
              (fun j => (C.centerLift j).val)
              (jointIntegerPhysicalSite (C.parameter t.val) (C.path.1.val, C.path.2.val))))) := by
    funext t
    rw [C.retainedParameter_parameter,
      C.chartValues_eq_physicalIntegerPoint hσ1 Cgeo hCgeo hchart hsmall hpoly t.val t.property]
    rfl
  rw [hf]
  exact hcorr

end AllocatedFrozenTaggedPairInput

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalLocalChart

theorem withKeep_localLaw {cost : ℝ} {Deck : Fin m → Type*}
    (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (keep : LayerSamplerVariables G I n B → Prop) (hkeep : C.keep = keep) :
    (C.withKeep keep hkeep).localLaw = C.localLaw := by
  cases hkeep
  rfl

end AllocatedExternalLocalChart

structure AllocatedExternalCandidateTaggedPairFamily
    (Deck : Fin m → Type*) (Ω Pivot : Type*) [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    (D : RationalFilteredNilmanifold LG s d₀)
    (E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j))
    (Fmark : NilpotentLieFiltration LM t) (φ : LG →ₗ⁅ℚ⁆ LM)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost p periodCap coverCap : ℝ) (Lip : ℝ≥0) where
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  hτ1 : τ ≤ 1
  hξ : ξ ≤ 1
  hσ1 : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x,
    ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8
  sourceChart : Ω → AllocatedExternalLocalChart (E := Deck) A cost
  keep_eq : ∀ a, (sourceChart a).keep = keep
  sourceCandidate : ∀ a, AllocatedExternalLocalCandidate (sourceChart a) D Fmark φ marked
  reference : Ω → Pivot → D.Niltest (fullTaggedVariableWeight (X := X) J)
  ambient : ∀ j, (E j).Niltest (fullTaggedVariableWeight (X := X) J)
  selected : ∀ j, (E j).Niltest (fullTaggedVariableWeight (X := X) J)
  selected_orbit : ∀ j, (selected j).orbit = (ambient j).orbit
  twist : Ω → Pivot → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip
  hp : 0 ≤ p
  hcost : cost ≤ p
  hperiod : ∀ a j, (((twist a j).modulus * (twist a j).cover : ℕ) : ℝ) ≤ Real.exp p
  hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : ∀ a j, (reference a j).ComplexityLE p
  hW : ∀ j, (selected j).ComplexityLE p
  hWnorm : ∀ j, (selected j).normBound ≤ 1
  η : Pivot → LG →ₗ[ℚ] ℚ
  θ : ∀ j, MG j →ₗ[ℚ] ℚ
  hηheight : ∀ j i, rationalLogHeight (η j (D.basis i)) ≤ p
  hθheight : ∀ j i, rationalLogHeight (θ j ((E j).basis i)) ≤ p
  hη : ∀ a j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    (reference a j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (reference a j).observable x
  hθ : ∀ j z, z ∈ (E j).filtration.realification.subgroup s → ∀ x,
    (selected j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (θ j) z.coord : ℝ) : CircleFourier.Circle) * (selected j).observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p
  hcorr : ∀ a j,
    let C := (sourceChart a).withKeep keep (keep_eq a)
    let candidate := (sourceCandidate a).withKeep keep (keep_eq a)
    Real.exp (-p) ≤ ‖(sourceChart a).localLaw.complexMean (fun site =>
      star ((twist a j).eval N poly (A.physical (sourceChart a).path site)) *
        ((reference a j).observable (candidate.value (C.retainedParameter site.val)) *
          (selected j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => ((sourceChart a).centerLift k).val)
            (A.physical (sourceChart a).path site))))‖

namespace AllocatedExternalCandidateTaggedPairFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type u} {MG : Pivot → Type u}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [∀ j, LieRing (MG j)] [∀ j, LieAlgebra ℚ (MG j)]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] MG j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] MG j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] MG j)] [∀ j, T2Space (ℝ ⊗[ℚ] MG j)]
    {s d₀ t : ℕ} {d : Pivot → ℕ}
    {D : RationalFilteredNilmanifold LG s d₀}
    {E : ∀ j, RationalFilteredNilmanifold (MG j) s (d j)}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateTaggedPairFamily A Deck Ω Pivot D E Fmark φ marked
      keep cost p periodCap coverCap Lip)

def context : AllocatedFrozenTaggedContext (G := G) (X := X) (J := J) B :=
  A.frozenTaggedContext F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    periodCap coverCap Lip

@[simp] theorem context_sides : F.context.sides keep = fun i => A.sides i.val := rfl

def chart (a : Ω) : AllocatedExternalLocalChart (E := Deck) A cost :=
  (F.sourceChart a).withKeep keep (F.keep_eq a)

def candidate (a : Ω) : AllocatedExternalLocalCandidate (F.chart a) D Fmark φ marked :=
  (F.sourceCandidate a).withKeep keep (F.keep_eq a)

@[simp] theorem chart_keep (a : Ω) : (F.chart a).keep = keep := rfl

@[simp] theorem chart_localLaw (a : Ω) : (F.chart a).localLaw = (F.sourceChart a).localLaw := by
  exact (F.sourceChart a).withKeep_localLaw A keep (F.keep_eq a)

def input (a : Ω) (j : Pivot) :
    AllocatedFrozenTaggedPairInput F.context Deck keep D (E j) p :=
  AllocatedFrozenTaggedPairInput.ofCandidate_of_localLaw A
    F.hpoly F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    (F.chart a) (F.candidate a) (F.reference a j) (F.selected j) (F.twist a j)
    F.hp F.hcost (F.hperiod a j) F.hvariation (F.hV a j) (F.hW j) (F.hWnorm j)
    (F.η j) (F.θ j) (F.hηheight j) (F.hθheight j) (F.hη a j) (F.hθ j) F.hK
    (by rw [F.chart_localLaw]; exact F.hcorr a j)

def jointOrbit (a : Ω) : ∀ i : Option Pivot,
    (optionFactors D E i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keep i} => 1)
  | none => (F.candidate a).orbit
  | some j => ((F.ambient j).integerChartPullback (fun _ : {i // keep i} => 1)
      (F.chart a).integerChart (F.chart a).integerChart_support).orbit

@[simp] theorem input_η (a : Ω) (j : Pivot) : (F.input a j).η = F.η j := rfl

@[simp] theorem input_θ (a : Ω) (j : Pivot) : (F.input a j).θ = F.θ j := rfl

@[simp] theorem input_V_orbit (a : Ω) (j : Pivot) :
    (F.input a j).V.orbit = (F.candidate a).orbit := rfl

theorem input_W_orbit (a : Ω) (j : Pivot) :
    (F.input a j).W.orbit = F.jointOrbit a (some j) := by
  change ((F.selected j).integerChartPullback (fun _ : {i // keep i} => 1)
    (F.chart a).integerChart (F.chart a).integerChart_support).orbit = _
  exact Niltest.integerChartPullback_orbit_eq_of_orbit_eq _ _ _ _ _ (F.selected_orbit j)

theorem pair_symbol (a : Ω) (j : Pivot)
    (c : Basis (Fin (finrank ℚ (PairAlgebra LG (MG j)))) ℚ (PairAlgebra LG (MG j)))
    (w : Fin (finrank ℚ (PairAlgebra LG (MG j))) → ℕ)
    (hc : ∀ k, (pi (pairModels D (E j))).filtration.layer k =
      Submodule.span ℚ (c '' {i | k ≤ w i})) :
    pairOrbitSymbol D (E j) (F.input a j).V.orbit (F.input a j).W.orbit c w hc =
      pairOrbitSymbol D (E j) (F.jointOrbit a none) (F.jointOrbit a (some j)) c w hc := by
  rw [F.input_V_orbit, F.input_W_orbit]
  rfl

end AllocatedExternalCandidateTaggedPairFamily

end

end Erdos3.VectorPolynomial

end

end OAI
