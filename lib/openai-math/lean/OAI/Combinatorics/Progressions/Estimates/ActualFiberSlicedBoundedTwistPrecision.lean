/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialDenseSliceCenter
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedModelPrecision
import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedSourceLog
import OAI.Combinatorics.Progressions.Probability.AllocatedFiberSlicedSourceLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "degree" => layerSamplerDegree I n
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Active" => {a : LayerSamplerAxis I n // ¬short a}
local notation "Input" => PrincipalTupleIndex B degree
local notation "ActiveInput" => PrincipalTupleIndex (fun a : Active => B (Subtype.val a))
  (fun a : Active => degree (Subtype.val a))

variable {keep : G ⊕ PrincipalTupleIndex B (layerSamplerDegree I n) → Prop} [DecidablePred keep]
variable {q : ℕ}
variable (slice : ResidueBoxSlice
  (fun k : {k // keep k} => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hlen : ∀ k, 0 < slice.length k) (fixed : {k // ¬keep k} → ℤ)
variable (hfixed : ∀ k, 0 ≤ fixed k ∧
  fixed k < ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))
variable (hkernel : ∀ g, keep (Sum.inl g))

variable (hactive : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val), keep (Sum.inr ⟨j.1.val, j.2⟩))

include hlen hfixed hactive in

theorem allocatedFiberActiveProgression_common_contained (j : ActiveInput) :
    integerProgressionSupport (slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (q : ℤ) (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩)) ⊆
        Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  simpa only [ResidueBoxSlice.fiberParameterStride, ite_eq_left (hactive j)] using
    allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed j

include hlen hfixed hactive in
theorem allocatedFiberActiveContainedProgression_eq_common
    (v : ∀ j : ActiveInput,
      IntegerScalarCubeBox Empty (slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))) :
    allocatedActiveContainedProgression B U basis S
      (fun j : ActiveInput => ResidueBoxSlice.fiberParameterStride
        (keep := keep) (q := q) (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedFiberActiveProgression_contained B U basis S slice hlen fixed hfixed) v =
    allocatedActiveContainedProgression B U basis S (fun _ => q)
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedFiberActiveProgression_common_contained B U basis S slice hlen fixed hfixed hactive) v := by
  funext j a
  apply Subtype.ext
  simp only [allocatedActiveContainedProgression, ResidueBoxSlice.fiberParameterStride,
    ite_eq_left (hactive j)]

theorem allocatedFiberPhysicalRoot_eq_raw
    (z : integerBox (Sum.elim (fun _ : G => S.value) sides)) :
    allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
      (kernelZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z)
      (principalZeroTupleFromSumIntegerBox B degree (fun _ : G => S.value) sides z) = z.val := by
  funext k
  cases k <;> simp only [allocatedPhysicalCubeRoot, Sum.elim_inl, Sum.elim_inr,
    kernelZeroTupleFromSumIntegerBox, principalZeroTupleFromSumIntegerBox, zero_add]

variable {X : Type*} [Fintype X]
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (base : X → ℤ) (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
variable (box : X → ℕ) (nativePoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hkernelLength : ∀ g, 2 ≤ slice.length ⟨Sum.inl g, hkernel g⟩)
variable (hactiveLength : ∀ j : PrincipalTupleIndex
  (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U basis S.value a} => B a.val)
  (fun a => layerSamplerDegree I n a.val),
  2 ≤ slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))

theorem allocatedFiberSliceLaw_native_complexMean :
    (slice.fiberSliceLaw hlen fixed hfixed).complexMean (fun z =>
      W.eval box nativePoly (fun a => base a + integerPhysicalSite z.val integerFrame a)) =
    allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
      (fun j => slice.fiberParameterLength (Sum.inr j))
      (fun j => ResidueBoxSlice.fiberParameterStride (keep := keep) (q := q) (Sum.inr j))
      (fun j => slice.fiberParameterStart fixed (Sum.inr j))
      (slice.fiberPrincipalParameter_inside hlen fixed hfixed)
      (fun j => slice.fiberParameterLength_pos hlen (Sum.inr j))
      (fun g => slice.length ⟨Sum.inl g, hkernel g⟩) hkernelLength
      (fun g => (slice.start ⟨Sum.inl g, hkernel g⟩ : ℤ)) q
      (slice.fiberKernelProgression_contained hkernel)
      (fun j : ActiveInput => slice.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => slice.fiberParameterStart fixed (Sum.inr ⟨j.1.val, j.2⟩))
      hactiveLength
      (allocatedFiberActiveProgression_common_contained B U basis S slice hlen fixed hfixed hactive) := by
  have he := allocatedFiberSliceLaw_sliced_source_complexMean B U basis S
    slice hlen fixed hfixed hkernel (fun x y => W.eval box nativePoly (fun a => base a +
      integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) integerFrame a))
  simp only [allocatedFiberPhysicalRoot_eq_raw] at he
  unfold allocatedSlicedNativeEvalMean
  refine he.trans ?_
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro u _
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro x _
  apply FiniteProbabilityWeights.complexMean_congr_support
  intro v _
  have hy := allocatedFiberActiveContainedProgression_eq_common B U basis S
    slice hlen fixed hfixed hactive v
  exact congrArg (fun y => W.eval box nativePoly (fun a => base a + integerPhysicalSite
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0)
        (fun g => containedProgressionCubeMap Empty S.value
          (slice.length ⟨Sum.inl g, hkernel g⟩) q (slice.start ⟨Sum.inl g, hkernel g⟩)
          S.positive (slice.fiberKernelProgression_contained hkernel g) (x g)) y) integerFrame a))
    (congrArg (principalAxisJoin short u) hy)

section ActualChild

variable {Hcut : ℕ} (hHcut : Hcut ≤ S.value)
variable (child : ResidueBoxSlice
  (fun k : {k : LayerSamplerVariables G I n B //
    Hcut ≤ Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k} =>
      Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val) q)
variable (hq : 0 < q) {cost : ℝ} (hlarge : 2 * Real.exp cost ≤ (S.value : ℝ))
variable (hfraction : ∀ k, Real.exp (-cost) *
  ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℝ) ≤
    child.length k)

include hHcut hq hlarge hfraction in
theorem allocatedChildFiber_active_length (j : ActiveInput) :
    2 ≤ child.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩) := by
  let k := allocatedChildNonshortCoordinate B U basis S hHcut j.1 j.2.1 j.2.2
  change 2 ≤ child.fiberParameterLength k.val
  rw [child.fiberParameterLength_of_keep _ k.property]
  exact (allocatedChildSlice_nonshort_geometry B U basis S hHcut child hq hlarge hfraction
    j.1 j.2.1 j.2.2).1

variable (hchildlen : ∀ k, 0 < child.length k)
variable (fixedChild : {k : LayerSamplerVariables G I n B //
  ¬Hcut ≤ Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k} → ℤ)
variable (hfixedChild : ∀ k, 0 ≤ fixedChild k ∧ fixedChild k <
  ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S) k.val : ℕ) : ℤ))

theorem allocatedChildFiberSliceLaw_native_complexMean :
    let hk := fun g => (allocatedChildKernelCoordinate B U basis S hHcut g).property
    let ha := fun j : ActiveInput =>
      (allocatedChildNonshortCoordinate B U basis S hHcut j.1 j.2.1 j.2.2).property
    (child.fiberSliceLaw hchildlen fixedChild hfixedChild).complexMean (fun z =>
      W.eval box nativePoly (fun a => base a + integerPhysicalSite z.val integerFrame a)) =
    allocatedSlicedNativeEvalMean B U basis S W base integerFrame box nativePoly
      (fun j => child.fiberParameterLength (Sum.inr j))
      (fun j => ResidueBoxSlice.fiberParameterStride
        (keep := fun k : LayerSamplerVariables G I n B =>
          Hcut ≤ Sum.elim (fun _ : G => S.value) sides k) (q := q) (Sum.inr j))
      (fun j => child.fiberParameterStart fixedChild (Sum.inr j))
      (child.fiberPrincipalParameter_inside hchildlen fixedChild hfixedChild)
      (fun j => child.fiberParameterLength_pos hchildlen (Sum.inr j))
      (fun g => child.length ⟨Sum.inl g, hk g⟩)
      (fun g => (allocatedChildSlice_kernel_geometry B U basis S hHcut child hq hlarge hfraction g).1)
      (fun g => (child.start ⟨Sum.inl g, hk g⟩ : ℤ)) q
      (child.fiberKernelProgression_contained hk)
      (fun j : ActiveInput => child.fiberParameterLength (Sum.inr ⟨j.1.val, j.2⟩))
      (fun j : ActiveInput => child.fiberParameterStart fixedChild (Sum.inr ⟨j.1.val, j.2⟩))
      (allocatedChildFiber_active_length B U basis S hHcut child hq hlarge hfraction)
      (allocatedFiberActiveProgression_common_contained B U basis S child hchildlen
        fixedChild hfixedChild ha) := by
  intro hk ha
  exact allocatedFiberSliceLaw_native_complexMean B U basis S child hchildlen
    fixedChild hfixedChild hk ha W base integerFrame box nativePoly
    (fun g => (allocatedChildSlice_kernel_geometry B U basis S hHcut child hq hlarge hfraction g).1)
    (allocatedChildFiber_active_length B U basis S hHcut child hq hlarge hfraction)

end ActualChild
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ δslice δbase PpresBase : ℝ}
variable {s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice}
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ)
  physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

omit [Fintype Tsp] in
theorem toDenseSliceMember_nativeMean :
    (path.toDenseSliceMember input).slice.nativeMean s W originalpoly =
      (input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) := by
  let member := path.toDenseSliceMember input
  have hactiveLength (j : PrincipalTupleIndex
      (fun a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) :
      2 ≤ input.box.fiberParameterLength (Sum.inr ⟨j.1.val,j.2⟩) :=
    member.slice.activeLength_two s.hδslice j.1 j.2
  exact (allocatedFiberSliceLaw_native_complexMean B U b S input.box input.length_pos
    input.fixed input.fixed_inside input.kernel_kept (fun j => input.active_kept j.1 j.2)
    W path.base path.noise physicalN (path.physicalPolynomial originalpoly)
    (fun g => (input.kernel_geometry g).1) hactiveLength).symm

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ δslice)
variable (num : ActualFixedSpatialSlicedForecastNumerics s)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv
  (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ)
  physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s num)

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : ((path.toDenseSliceMember input).slice).path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {t δ ε η : ℝ} (ht : 0 < t) (hσbound : ∀ j, |σ j| ≤ t)
variable (hδ : 0 < δ) (hδone : δ ≤ 1)
variable (hdense : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), δ * S.value ≤
    ((integerProgressionSupport (((path.toDenseSliceMember input).slice).principalStart ⟨a.val,p⟩) (((path.toDenseSliceMember input).slice).step : ℤ)
      (((path.toDenseSliceMember input).slice).principalLength ⟨a.val,p⟩)).card : ℝ))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ ((path.toDenseSliceMember input).slice).path.referenceModulus)
variable (hsizeG : ∀ g, q ≤ ((path.toDenseSliceMember input).slice).kernelLength g)
variable (hsmallG : ∀ g, scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / ((path.toDenseSliceMember input).slice).kernelLength g) < 1)
variable (hsize : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val), q ≤ ((path.toDenseSliceMember input).slice).principalLength ⟨a.val,p⟩)
variable (hsmall : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
    scalarCubeGridBoundaryConstant Empty * ((q : ℝ) / ((path.toDenseSliceMember input).slice).principalLength ⟨a.val,p⟩) < 1)
variable (hε : 0 ≤ ε) (hmesh : (((path.toDenseSliceMember input).slice).step : ℝ) / S.value ≤ ε)
variable (hη : 0 < η)
variable (htail : |t| * polynomialMassC2Budget
  (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val))) m 1 ≤
  slicedPrincipalC2Tolerance
    (Fintype.card (Σ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      B a.val × Fin (layerSamplerDegree I n a.val)))
    (Fintype.card {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}) m 1
    (unitProfilePrincipalLowerBound B) (δ / 2) s.L η)

variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : ((path.toDenseSliceMember input).slice).path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata Ptest : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (((path.toDenseSliceMember input).slice).path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value ((∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ))) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖((path.toDenseSliceMember input).slice).targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Eprec Rrank : ℝ} (hEprec : 0 ≤ Eprec)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) Eprec + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (cutoff : ℕ) (hcutoff : 0 < cutoff)
variable {δgrid : ℝ} (hδgrid : 0 ≤ δgrid) (hδgrid1 : δgrid ≤ 1)
variable (hgridmesh : ∀ j, ((q * cutoff : ℕ) : ℝ) /
  forecastJointGridScale U b R S.value physicalN τ j ≤ δgrid)
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center ((path.toDenseSliceMember input).slice).path.center ((path.toDenseSliceMember input).slice).path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center ((path.toDenseSliceMember input).slice).path.base ((path.toDenseSliceMember input).slice).path.noise ≠ 0)
variable (hsampleAt : sampleFn ((path.toDenseSliceMember input).slice).path.noise = ((path.toDenseSliceMember input).slice).path.sample)
variable (hreadAt : readFn ((path.toDenseSliceMember input).slice).path.noise = ((path.toDenseSliceMember input).slice).path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = ((path.toDenseSliceMember input).slice).target (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe ht hσbound hδ hδone hdense hperiod hcover hqN
  hsizeG hsmallG hsize hsmall hε hmesh hη htail ν hlattice hcompact hmargin htrimbase
  hcenter hκ hUniversal hPtest hLw hpw hcw hEprec hlarge hRrank hrank hcutoff hδgrid
  hδgrid1 hgridmesh hglobal hz hsampleAt hreadAt hfinite htarget in

theorem denseFiber_ambient_model_comparison :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      ((path.toDenseSliceMember input).slice).comparisonError (Lip := Lip) (ξ := ξ) (t := t) (δ := δ) (ε := ε) (η := η) (q := q)
        (hδ := hδ) (o := o) (δnative := Real.exp (-Edata)) (M := Real.exp massLog)
        (Eprec := Eprec) (cutoff := cutoff) (δgrid := δgrid) := by
  have hc := ((path.toDenseSliceMember input).slice).native_ambient_model_comparison
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox)
    (hframe := hframe) (ht := ht) (hσbound := hσbound) (hδ := hδ) (hδone := hδone)
    (hdense := hdense) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (hsizeG := hsizeG) (hsmallG := hsmallG) (hsize := hsize) (hsmall := hsmall)
    (hε := hε) (hmesh := hmesh) (hη := hη) (htail := htail)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (cutoff := cutoff) (hcutoff := hcutoff) (hδgrid := hδgrid) (hδgrid1 := hδgrid1)
    (hgridmesh := hgridmesh) (C := C) (hglobal := hglobal) (hz := hz)
    (hsampleAt := hsampleAt) (hreadAt := hreadAt) (hfinite := hfinite) (htarget := htarget)
  rw [path.toDenseSliceMember_nativeMean input W originalpoly] at hc
  exact hc

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {Pnative massLog capLog Edata : ℝ}
variable (data : ActualForecastData physicalN originalpoly Pnative massLog capLog Edata)
variable (hcenter : data.centerConstant = fun j => (path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖(path.toDenseSliceMember input).slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, data.coefficient i * (data.twists i).eval physicalN
      (fun j => subtractConstant (data.centerConstant j) (poly j)) u‖ ≤ Real.exp (-Edata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * Pnative + 3) + 1)) (massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (htarget : data.target = (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ Edata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hcenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite htarget
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match in

theorem denseFiber_ambient_model_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (data.centerConstant j) (originalpoly j)) u.val * data.target u)‖ ≤
      Real.exp (-E) := by
  obtain ⟨hPu, hDsq, hAL, htest⟩ := s.slicedComparisonSourceLog_bounds Ptest
  have hLip := hLw.trans (Real.exp_le_exp.mpr htest)
  have hHP : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      ∀ p : B a.val × Fin (layerSamplerDegree I n a.val),
        Real.exp (-cost) * S.value ≤
          ((path.toDenseSliceMember input).slice.principalLength ⟨a.val,p⟩ : ℝ) := by
    intro a p
    change Real.exp (-cost) * S.value ≤
      (input.box.fiberParameterLength (Sum.inr ⟨a.val,p⟩) : ℝ)
    rw [input.box.fiberParameterLength_of_keep _ (input.active_kept a p)]
    simpa only [Sum.elim_inr, allocatedPrincipalSides_not_short B U b S a p, hcost_match]
      using input.dense ⟨Sum.inr ⟨a.val,p⟩, input.active_kept a p⟩
  have hHG : ∀ g, Real.exp (-cost) * S.value ≤
      ((path.toDenseSliceMember input).slice.kernelLength g : ℝ) := by
    intro g
    change Real.exp (-cost) * S.value ≤ (input.box.length ⟨Sum.inl g,input.kernel_kept g⟩ : ℝ)
    simpa only [Sum.elim_inl, hcost_match] using input.dense ⟨Sum.inl g,input.kernel_kept g⟩
  have hstep : ((path.toDenseSliceMember input).slice.step : ℝ) ≤ 2 * Real.exp cost := by
    change (input.step : ℝ) ≤ 2 * Real.exp cost
    simpa only [hcost_match] using input.step_le
  have hcomp := (path.toDenseSliceMember input).slice.native_ambient_model_precision
    (s := s) (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := data) (hcenter := hcenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (htarget := htarget) (hcost := hcost) (hPu := hPu) (hE := hE)
    (hDsq := hDsq) (hAL := hAL) (hτ1 := hτ1) (hLip := hLip) (hq := hq) (hfloor := hfloor)
    (hHP := hHP) (hHG := hHG) (hstep := hstep) (hξsmall := hξsmall) (hEdata := hEdata)
    (hNgrid := hNgrid)
  rw [path.toDenseSliceMember_nativeMean input W originalpoly] at hcomp
  exact hcomp

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable {latePnative lateMassLog lateCapLog lateEdata : ℝ}
variable (lateData : ActualForecastData physicalN originalpoly latePnative lateMassLog lateCapLog lateEdata)
variable (hLateCenter : lateData.centerConstant = fun j => (path.center j).val)
variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hUniversal : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
  (hm : ∀ j d, coefficients (poly j) d ∈ U j) (u : X → ℤ),
  ‖(path.toDenseSliceMember input).slice.targetAt (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb poly hm s.κ u -
    ∑ i, lateData.coefficient i * (lateData.twists i).eval physicalN
      (fun j => subtractConstant (lateData.centerConstant j) (poly j)) u‖ ≤ Real.exp (-lateEdata))
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ lateMassLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * latePnative + 3) + 1)) (lateMassLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * latePnative + 3) + 1)) (lateMassLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hLateTarget : lateData.target = (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
  s.hBactive o bW hb originalpoly hmem s.κ)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ lateEdata)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hLateCenter hκ hUniversal hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite hLateTarget
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget in

theorem denseFiber_ambient_early_model_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (earlyData.centerConstant j) (originalpoly j)) u.val *
            earlyData.target u)‖ ≤ Real.exp (-E) := by
  have hc := denseFiber_ambient_model_precision
    (s := s) (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (data := lateData) (hcenter := hLateCenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (htarget := hLateTarget) (hcost := hcost) (hE := hE)
    (hτ1 := hτ1) (hq := hq) (hfloor := hfloor) (hξsmall := hξsmall)
    (hEdata := hEdata) (hNgrid := hNgrid)
  have hcenterEq : lateData.centerConstant = earlyData.centerConstant :=
    hLateCenter.trans hEarlyCenter.symm
  have htargetEq : lateData.target = earlyData.target := hLateTarget.trans hEarlyTarget.symm
  simpa only [hcenterEq, htargetEq] using hc

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget hδlate hHlate hvlate hTaillate in

theorem denseFiber_ambient_constructed_late_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN (path.physicalPolynomial originalpoly)
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN
          (fun j => subtractConstant (earlyData.centerConstant j) (originalpoly j)) u.val *
            earlyData.target u)‖ ≤ Real.exp (-E) := by
  obtain ⟨lateData, hLateTarget, hLateCenter, hUniversal⟩ :=
    exists_actualSlicedForecast_late_data s qnum qLate o bW hb originalpoly hmem
      (path.toDenseSliceMember input) hδlate hHlate hvlate hTaillate
  exact denseFiber_ambient_early_model_precision
    (s := s) (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW) (W := W) (originalpoly := originalpoly)
    (hmem := hmem) (hdegree := hdegree) (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (lateData := lateData) (hLateCenter := hLateCenter) (hκ := hκ) (hUniversal := hUniversal)
    (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (hLateTarget := hLateTarget) (hcost := hcost) (hE := hE)
    (hτ1 := hτ1) (hq := hq) (hfloor := hfloor) (hξsmall := hξsmall)
    (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hEarlyTarget := hEarlyTarget)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {V E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable (q : ℕ) [NeZero q]
variable (hperiod : W.modulus ∣ q) (hcover : W.cover ∣ q)
variable (hqN : q ∣ path.referenceModulus)
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hq : (q : ℝ) ≤ Real.exp V)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) V E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) V s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget hδlate hHlate hvlate hTaillate in

theorem denseFiber_ambient_original_twist_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  have hc := denseFiber_ambient_constructed_late_precision
    (s := s) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate)
    (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW)
    (W := W.shiftConstant (fun j => -(path.center j).val))
    (originalpoly := originalpoly) (hmem := hmem) (hdegree := hdegree)
    (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (hcost := hcost) (hE := hE) (hτ1 := hτ1) (hq := hq)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hEarlyTarget := hEarlyTarget)
  simpa only [NormalizedPolynomialTwist.eval_shiftConstant, physicalPolynomial,
    hEarlyCenter, subtractConstant_neg_cancel] using hc

include hR hσ hdegree hξ hbox hframe hσbound hperiod hcover hqN
  ν hlattice hcompact hmargin htrimbase hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite
  hcost hE hτ1 hq hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget hδlate hHlate hvlate hTaillate in

theorem denseFiber_ambient_original_star_twist_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => star (W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite z.val path.noise a))) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => star (W.eval physicalN originalpoly u.val) * earlyData.target u)‖ ≤ Real.exp (-E) := by
  have hc := denseFiber_ambient_original_twist_precision
    (s := s) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate)
    (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW)
    (W := W)
    (originalpoly := originalpoly) (hmem := hmem) (hdegree := hdegree)
    (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q) (hperiod := hperiod) (hcover := hcover) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (hcost := hcost) (hE := hE) (hτ1 := hτ1) (hq := hq)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hEarlyTarget := hEarlyTarget)
  have htarget (u : integerBox physicalN) : star (earlyData.target u) = earlyData.target u := by
    rw [hEarlyTarget]
    exact (path.toDenseSliceMember input).slice.target_star
      (allocatedShortIntegerSelection U b S.value) s.hBactive o bW hb s.κ originalpoly hmem u
  rw [FiniteProbabilityWeights.complexMean_star]
  have hmean :
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => star (W.eval physicalN originalpoly u.val) * earlyData.target u) =
      star ((FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)) := by
    rw [← FiniteProbabilityWeights.complexMean_star]
    congr 1
    funext u
    rw [star_mul, htarget]
    exact mul_comm _ _
  rw [hmean, ← star_sub, norm_star]
  exact hc

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod Lrank : ℕ} {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩}
variable {Tsp : Type} [Fintype Tsp] {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)}
variable {physicalN : X → ℕ} {τ cost : ℝ}
variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod (allocatedShortIntegerSelection U b S.value) τ (Real.exp (-cost) / 2))
variable {qnum : ActualFixedSpatialSlicedForecastNumerics s}
variable (qLate : ActualFixedSpatialSlicedForecastNumerics s)
variable (hδlate : qnum.δ = qLate.δ) (hHlate : qnum.Hchild = qLate.Hchild)
variable (hvlate : qnum.v = qLate.v) (hTaillate : qnum.Ptail = qLate.Ptail)
variable {δbase PpresBase : ℝ}
variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
  (S.value : ℝ) physicalN τ δbase s.P s.Pbad PpresBase)
variable (input : ActualFixedSpatialDenseSliceInput s qnum)
variable (hcost_match : input.cost = cost)

namespace ActualFixedSpatialForecastPath

variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}
variable (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
variable (originalpoly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j d, coefficients (originalpoly j) d ∈ U j)
variable (hdegree : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (originalpoly j))
variable (ξ : ℝ) (hξ : 0 < ξ)
variable (hbox : ∀ x, 0 < physicalN x)
variable (hframe : path.noise ∈ rectangularWeightIndices 0
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n))
    (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ physicalN) 1)
variable {E Ptest : ℝ}
variable (hσbound : ∀ j, |σ j| ≤ Real.exp (-fixedPathSlicedPerturbationLog
  s.D (s.D + (s.slicedComparisonSourceLog Ptest) + 4) (cost + 1) (2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14) m))
variable [hlattice : ∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
  (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable [hcompact : CompactSpace (EuclideanJetLayers U (fun _ : Fin m => Unit))]
variable (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
variable (htrimbase : path.base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))

variable (hκ : s.κ = forecastGeometricJacobian (X := X) (I := I) U b R S.value (∏ a, (basisAxisScale (b ((allocatedShortIntegerSelection U b S.value) a).1) ((allocatedShortIntegerSelection U b S.value) a).2 : ℝ)) τ)
variable (hPtest : 0 ≤ Ptest) (hLw : (Lip : ℝ) ≤ Real.exp Ptest)
variable (hpw : periodCap ≤ Real.exp Ptest) (hcw : coverCap ≤ Real.exp Ptest)
variable {Rrank : ℝ} (hEprec : 0 ≤ qLate.massLog + E + 8)
variable (hlarge : ∀ i, Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ (physicalN i : ℝ))
variable (hRrank : Real.exp ((max (max s.P (2 * max Ptest (3 * qLate.Pnative + 3) + 1)) (qLate.massLog + E + 8) + nativeForecastAmbientExponent m) ^
  nativeForecastAmbientExponent m) ≤ Rrank)
variable (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (physicalN i : ℝ))
  Rrank (U j) (originalpoly j))
variable (C : ℝ)
variable {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
variable {sampleFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n}
variable {readFn : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
  AllocatedActualCoefficientIndex G X I Eout n B → ℤ}
variable (hglobal : AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
  originalpoly hmem (allocatedShortAxis (I := I) U b S.value) spatial kernel block C
  center path.center path.base sampleFn readFn)
variable (hz : allocatedCenteredJointDensity B U b hb o hR hσ S originalpoly hmem
  center path.base path.noise ≠ 0)
variable (hsampleAt : sampleFn path.noise = path.sample)
variable (hreadAt : readFn path.noise = path.read)

variable (hfinite : (integerBox physicalN).Nonempty)
variable (hcost : 0 ≤ cost) (hE : 0 ≤ E)
variable (hτ1 : τ ≤ 1)
variable (hfloor : ActualFixedSpatialSlicedForecastPath.comparisonPrecisionFloor s (Dmod + Fintype.card (Σ j, I j)) (s.slicedComparisonSourceLog Ptest) (2 * Ptest) E ≤ S.value)
variable (hξsmall : ξ ≤ Real.exp (-(2 * (s.slicedComparisonSourceLog Ptest) + (E + 4) + 14)))
variable (hEdata : E + 8 ≤ qLate.E)
variable (hNgrid : ∀ i, Real.exp (forecastJointGridAmbientLog
  (Dmod + Fintype.card (Σ j, I j)) (ActualFixedSpatialSlicedForecastPath.comparisonGridLog s (s.slicedComparisonSourceLog Ptest))
  (E + 4) (2 * Ptest) s.Pτ) ≤ (physicalN i : ℝ))

variable {earlyPnative earlyMassLog earlyCapLog earlyEdata : ℝ}
variable (earlyData : ActualForecastData physicalN originalpoly
  earlyPnative earlyMassLog earlyCapLog earlyEdata)
variable (hEarlyCenter : earlyData.centerConstant = fun j => (path.center j).val)
variable (hEarlyTarget : earlyData.target =
  (path.toDenseSliceMember input).slice.target (allocatedShortIntegerSelection U b S.value)
    s.hBactive o bW hb originalpoly hmem s.κ)

variable (hprimes : path.primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊)
variable (hexponent : path.exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)

include hR hσ hdegree hξ hbox hframe hσbound
  ν hlattice hcompact hmargin htrimbase hκ hPtest hLw hpw hcw
  hEprec hlarge hRrank hrank hglobal hz hsampleAt hreadAt hfinite
  hcost hE hτ1 hfloor hξsmall hEdata hNgrid hcost_match hEarlyCenter hEarlyTarget
  hδlate hHlate hvlate hTaillate hprimes hexponent in

theorem denseFiber_ambient_bounded_original_twist_precision :
    ‖(input.box.fiberSliceLaw input.length_pos input.fixed input.fixed_inside).complexMean
        (fun z => W.eval physicalN originalpoly
          (fun a => path.base a + integerPhysicalSite z.val path.noise a)) -
      (FiniteProbabilityWeights.uniformFinset (integerBox physicalN) hfinite).complexMean
        (fun u => W.eval physicalN originalpoly u.val * earlyData.target u)‖ ≤ Real.exp (-E) := by
  let q := W.modulus * W.cover
  have hqpos : 0 < q := Nat.mul_pos W.modulus_pos W.cover_pos
  let : NeZero q := ⟨hqpos.ne'⟩
  have hq : (q : ℝ) ≤ Real.exp (2 * Ptest) := by
    calc
      (q : ℝ) = (W.modulus : ℝ) * (W.cover : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp Ptest * Real.exp Ptest := mul_le_mul
        (W.modulus_bound.trans hpw) (W.cover_bound.trans hcw)
        (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * Ptest) := by rw [← Real.exp_add]; congr 1; ring
  have hqNat : q ≤ ⌈Real.exp (2 * Ptest)⌉₊ := by
    exact_mod_cast hq.trans (Nat.le_ceil _)
  have hqN : q ∣ path.referenceModulus :=
    path.dvd_referenceModulus_of_le_bound _ hprimes hexponent hqpos hqNat
  exact denseFiber_ambient_original_twist_precision
    (s := s) (qLate := qLate) (hδlate := hδlate) (hHlate := hHlate)
    (hvlate := hvlate) (hTaillate := hTaillate)
    (path := path) (input := input) (hcost_match := hcost_match)
    (hb := hb) (o := o) (bW := bW) (W := W)
    (originalpoly := originalpoly) (hmem := hmem) (hdegree := hdegree)
    (ξ := ξ) (hξ := hξ) (hbox := hbox) (hframe := hframe)
    (hσbound := hσbound) (q := q)
    (hperiod := Nat.dvd_mul_right _ _) (hcover := Nat.dvd_mul_left _ _) (hqN := hqN)
    (ν := ν) (hmargin := hmargin) (htrimbase := htrimbase)
    (hκ := hκ) (hPtest := hPtest) (hLw := hLw) (hpw := hpw) (hcw := hcw)
    (hEprec := hEprec) (hlarge := hlarge) (hRrank := hRrank) (hrank := hrank)
    (C := C) (hglobal := hglobal) (hz := hz) (hsampleAt := hsampleAt) (hreadAt := hreadAt)
    (hfinite := hfinite) (hcost := hcost) (hE := hE) (hτ1 := hτ1) (hq := hq)
    (hfloor := hfloor) (hξsmall := hξsmall) (hEdata := hEdata) (hNgrid := hNgrid)
    (earlyData := earlyData) (hEarlyCenter := hEarlyCenter) (hEarlyTarget := hEarlyTarget)

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
