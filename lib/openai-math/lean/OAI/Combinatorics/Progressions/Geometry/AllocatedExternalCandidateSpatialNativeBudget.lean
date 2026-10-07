import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrecenterNativePartners
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedSourceEvaluation
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalRetainedResidual
import OAI.Combinatorics.Progressions.Probability.NativeSliceLawVerticalPartners

namespace OAI

section

namespace Erdos3.VectorPolynomial

def spatialNativeVerticalParameter (pNative pLocal r : ℝ) : ℝ :=
  max pNative 0 + pLocal + r + 1

def spatialNativeFactorParameter (p pNative pLocal r : ℝ) : ℝ :=
  max p (r + verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) + 2)

theorem spatialNativeVerticalFactorBounds (p pNative pLocal r : ℝ)
    (hlocal : 0 ≤ pLocal) (hr : 0 ≤ r) :
    0 ≤ spatialNativeVerticalParameter pNative pLocal r ∧
    pNative ≤ spatialNativeVerticalParameter pNative pLocal r ∧
    pLocal + r + 1 ≤ spatialNativeVerticalParameter pNative pLocal r ∧
    p ≤ spatialNativeFactorParameter p pNative pLocal r ∧
    0 ≤ spatialNativeFactorParameter p pNative pLocal r ∧
    verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) ≤
      spatialNativeFactorParameter p pNative pLocal r ∧
    r + verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) + 2 ≤
      spatialNativeFactorParameter p pNative pLocal r := by
  have hmax0 : 0 ≤ max pNative 0 := le_max_right _ _
  have hmax : pNative ≤ max pNative 0 := le_max_left _ _
  have hvertical : 0 ≤ spatialNativeVerticalParameter pNative pLocal r := by
    unfold spatialNativeVerticalParameter
    linarith only [hmax0, hlocal, hr]
  have hdecomp := verticalDecompositionBudget_nonneg hvertical
  have hright : r + verticalDecompositionBudget
      (spatialNativeVerticalParameter pNative pLocal r) + 2 ≤
        spatialNativeFactorParameter p pNative pLocal r := le_max_right _ _
  refine ⟨hvertical, ?_, ?_, le_max_left _ _, ?_, ?_, hright⟩
  · unfold spatialNativeVerticalParameter
    linarith only [hmax, hlocal, hr]
  · unfold spatialNativeVerticalParameter
    linarith only [hmax0]
  · exact (by linarith only [hr, hdecomp] :
      0 ≤ r + verticalDecompositionBudget
        (spatialNativeVerticalParameter pNative pLocal r) + 2).trans hright
  · exact (by linarith only [hr] :
      verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) ≤
        r + verticalDecompositionBudget
          (spatialNativeVerticalParameter pNative pLocal r) + 2).trans hright

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*)

noncomputable def fullTaggedSpatialIntegerChart (x : X) : MvPolynomial (X ⊕ (Σ j, J j)) ℤ :=
  MvPolynomial.X (Sum.inl x)

theorem fullTaggedSpatialIntegerChart_support (x : X) :
    integerSampledRealChart (fullTaggedSpatialIntegerChart (X := X) J) x ∈
      weightedSupportLE (fullTaggedVariableWeight J) 1 := by
  change MvPolynomial.map (Int.castRingHom ℝ) (MvPolynomial.X (Sum.inl x)) ∈ _
  rw [MvPolynomial.map_X]
  exact weightedSupportLE_X (fullTaggedVariableWeight J) (Sum.inl x)

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}
    (Q : D.Niltest (fun _ : X => 1)) (J : Fin m → Type*)

noncomputable def fullTaggedSpatial : D.Niltest (fullTaggedVariableWeight (X := X) J) :=
  Q.integerChartPullback (fullTaggedVariableWeight J) (fullTaggedSpatialIntegerChart J)
    (fullTaggedSpatialIntegerChart_support J)

@[simp] theorem fullTaggedSpatial_eval (u : X ⊕ (Σ j, J j) → ℤ) :
    (Q.fullTaggedSpatial J).eval u = Q.eval (fun x => u (Sum.inl x)) := by
  rw [fullTaggedSpatial, integerChartPullback_eval]
  simp only [fullTaggedSpatialIntegerChart, MvPolynomial.eval_X]

@[simp] theorem fullTaggedSpatial_eval_physical
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (u : X → ℤ) :
    (Q.fullTaggedSpatial J).eval (fullTaggedPhysicalIntegerPoint J poly c u) = Q.eval u := by
  rw [fullTaggedSpatial_eval]
  rfl

@[simp] theorem fullTaggedSpatial_normBound :
    (Q.fullTaggedSpatial J).normBound = Q.normBound := rfl

@[simp] theorem fullTaggedSpatial_complexity (p : ℝ) :
    (Q.fullTaggedSpatial J).ComplexityLE p ↔ Q.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

namespace Erdos3.NativeSampleModel

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {m s : ℕ} {X T : Type*} {p : ℝ}
    {sample : T → X → ℤ} {f : T → ℂ}
    (Q : NativeSampleModel (fun _ : X => 1) s p sample f)
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

noncomputable def fullTaggedSpatial (c : ∀ j, J j → ℝ) :
    NativeSampleModel (fullTaggedVariableWeight J) s p
      (fun t => fullTaggedPhysicalIntegerPoint J poly c (sample t)) f where
  L := Q.L
  dim := Q.dim
  model := Q.model
  test := Q.test.fullTaggedSpatial J
  norm := Q.norm
  complexity := Q.complexity
  eval t := by
    rw [RationalFilteredNilmanifold.Niltest.fullTaggedSpatial_eval_physical]
    exact Q.eval t

theorem fullTaggedSpatial_test_independent (c c' : ∀ j, J j → ℝ) :
    (Q.fullTaggedSpatial J poly c).test = (Q.fullTaggedSpatial J poly c').test := rfl

theorem fullTaggedSpatial_orbit_independent (c c' : ∀ j, J j → ℝ) :
    (Q.fullTaggedSpatial J poly c).test.orbit =
      (Q.fullTaggedSpatial J poly c').test.orbit := rfl

end Erdos3.NativeSampleModel

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators Classical

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

theorem exists_spatialNative_slice_tagged_vertical_partners
    {Ω Pivot K X T LG : Type*} [Fintype Ω] [Fintype Pivot] [Fintype K] [DecidableEq K]
    [LieRing LG] [LieAlgebra ℚ LG]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {m s d : ℕ} (J : Fin m → Type*)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (D : RationalFilteredNilmanifold LG s d)
    {pNative : ℝ} (sample : T → X → ℤ)
    (nativeValue : Pivot → T → ℂ)
    (native : ∀ j, NativeSampleModel (fun _ : X => 1) s pNative sample (nativeValue j))
    (P : Ω → Pivot → D.Niltest (fun _ : K => 1))
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {N : K → ℕ} (stride : Ω → Pivot → ℕ)
    (S : ∀ a j, ResidueBoxSlice N (stride a j))
    (hstride : ∀ a ∈ H, ∀ j, 0 < stride a j)
    (hlen : ∀ a j i, 0 < (S a j).length i)
    (physical : Ω → integerBox N → T)
    (center : Ω → ∀ j, J j → ℝ)
    (twist : Ω → Pivot → integerBox N → ℂ)
    {pLocal r q : ℝ} (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r) (hpq : pNative ≤ q)
    (hprecision : pLocal + r + 1 ≤ q)
    (hP : ∀ a ∈ H, ∀ j, (P a j).ComplexityLE pLocal)
    (htwist : ∀ a ∈ H, ∀ j t, ‖twist a j t‖ ≤ 1)
    (hcorr : ∀ a ∈ H, ∀ j, Real.exp (-r) ≤
      ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        (star (twist a j t) * nativeValue j (physical a t)) * (P a j).eval t.val)‖) :
    ∃ (freq : ∀ j, (native j).L →ₗ[ℚ] ℚ)
      (V : ∀ j, (native j).model.Niltest (fullTaggedVariableWeight (X := X) J))
      (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card Pivot) * outer.mass H ≤
        outer.mass retained ∧
      (∀ j, (V j).orbit = ((native j).test.fullTaggedSpatial J).orbit ∧
        (V j).ComplexityLE pNative ∧ (V j).normBound ≤ 1) ∧
      (∀ j i, rationalLogHeight (freq j ((native j).model.basis i)) ≤
        verticalDecompositionBudget q) ∧
      (∀ j z, z ∈ (native j).model.filtration.realification.subgroup s → ∀ x,
        (V j).observable (z • x) = character
          ((realifyFunctional (freq j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x) ∧
      ∀ a ∈ retained, ∀ j,
        Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) ≤
          ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
            star (twist a j t) * ((P a j).eval t.val *
              (V j).eval (fullTaggedPhysicalIntegerPoint J poly (center a)
                (sample (physical a t)))))‖ := by
  have hnativeCorr (a : Ω) (ha : a ∈ H) (j : Pivot) :
      Real.exp (-r) ≤ ‖((S a j).fullSliceLaw (hlen a j)).complexMean (fun t =>
        ((P a j).eval t.val * star (twist a j t)) *
          (native j).test.eval (sample (physical a t)))‖ := by
    convert hcorr a ha j using 2
    congr 1
    funext t
    rw [(native j).eval]
    ring
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, _hint,
      _hpres, hselected⟩ := exists_sliceLaw_localPivot_weighted_native_vertical_partners
    (fun j => (native j).model) (fun _ _ => D) (fun j => (native j).test) P
    outer H hH stride S hstride hlen (fun a t => sample (physical a t)) (fun _ _ t => t.val)
    (fun a j t => star (twist a j t)) hpLocal hr hpq hprecision
    (fun j => (native j).complexity) (fun j => by exact_mod_cast (native j).norm)
    hP (fun a ha j t => by simpa only [norm_star] using htwist a ha j t) hnativeCorr
  refine ⟨freq, (fun j => (V j).fullTaggedSpatial J), retained,
    hsub, hpos, hmass, ?_, hheight, hvert, ?_⟩
  · intro j
    refine ⟨?_, (hcert j).1, ?_⟩
    · simp only [Niltest.fullTaggedSpatial, Niltest.integerChartPullback,
        Niltest.withOrbit, (hcert j).2.1]
    · exact_mod_cast (hcert j).2.2.2.2
  · intro a ha j
    convert hselected a ha j using 2
    congr 1
    funext t
    rw [Niltest.fullTaggedSpatial_eval_physical]
    ring

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

structure AllocatedExternalCandidateSpatialNativeFamily
    (Deck : Fin m → Type*) (Ω Pivot : Type*) [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ}
    (D : RationalFilteredNilmanifold LG s d₀)
    (Fmark : NilpotentLieFiltration LM t) (φ : LG →ₗ⁅ℚ⁆ LM)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost p pLocal pNative r periodCap coverCap : ℝ) (Lip : ℝ≥0) where
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
  nativeValue : Pivot → integerBox N → ℂ
  native : ∀ j, NativeSampleModel (fun _ : X => 1) s pNative
    (fun x : integerBox N => x.val) (nativeValue j)
  twist : Ω → Pivot → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip
  hp : 0 ≤ p
  hpLocal : 0 ≤ pLocal
  hr : 0 ≤ r
  hcost : cost ≤ p
  hlocal : pLocal ≤ p
  hnative : pNative ≤ p
  hperiod : ∀ a j, (((twist a j).modulus * (twist a j).cover : ℕ) : ℝ) ≤ Real.exp p
  hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
    ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p
  hV : ∀ a j, (reference a j).ComplexityLE pLocal
  η : Pivot → LG →ₗ[ℚ] ℚ
  hηheight : ∀ j i, rationalLogHeight (η j (D.basis i)) ≤ p
  hη : ∀ a j z, z ∈ D.filtration.realification.subgroup s → ∀ x,
    (reference a j).observable (z • x) = CircleFourier.character
      ((realifyFunctional (η j) z.coord : ℝ) : CircleFourier.Circle) * (reference a j).observable x
  hK : (Fintype.card {i // keep i} : ℝ) ≤ p

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def chart (a : Ω) : AllocatedExternalLocalChart (E := Deck) A cost :=
  (F.sourceChart a).withKeep keep (F.keep_eq a)

def candidate (a : Ω) : AllocatedExternalLocalCandidate (F.chart a) D Fmark φ marked :=
  (F.sourceCandidate a).withKeep keep (F.keep_eq a)

def localTest (a : Ω) (j : Pivot) : D.Niltest (fun _ : {i // keep i} => 1) :=
  (F.reference a j).withOrbit (F.candidate a).orbit

def jointOrbit (a : Ω) : ∀ i : Option Pivot,
    (optionFactors D (fun j => (F.native j).model) i).filtration.realification.PolynomialOrbit
      (fun _ : {i // keep i} => 1)
  | none => (F.candidate a).orbit
  | some j => (((F.native j).test.fullTaggedSpatial J).integerChartPullback
      (fun _ : {i // keep i} => 1)
      (F.chart a).integerChart (F.chart a).integerChart_support).orbit

def physicalBox (a : Ω) (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    integerBox N :=
  ⟨A.physical (F.chart a).path ((F.chart a).site u.val u.property),
    A.physical_mem_integerBox F.hξ _ _⟩

@[simp] theorem physicalBox_val (a : Ω)
    (u : integerBox (fun i : {i // keep i} => A.sides i.val)) :
    (F.physicalBox a u).val = (F.chart a).physical u.val := rfl

def sitePhysicalBox (a : Ω) (site : A.Site) : integerBox N :=
  ⟨A.physical (F.sourceChart a).path site,
    A.physical_mem_integerBox F.hξ _ _⟩

def correlation (a : Ω) (j : Pivot) : ℂ :=
  (F.sourceChart a).localLaw.complexMean (fun site =>
    star ((F.twist a j).eval N poly (F.sitePhysicalBox a site).val) *
      ((F.reference a j).observable ((F.sourceCandidate a).siteValue site) *
        F.nativeValue j (F.sitePhysicalBox a site)))

@[simp] theorem chart_localLaw (a : Ω) :
    (F.chart a).localLaw = (F.sourceChart a).localLaw :=
  (F.sourceChart a).withKeep_localLaw A keep (F.keep_eq a)

theorem rawCorrelation_fullSliceLaw (a : Ω) (j : Pivot)
    (hcorr : Real.exp (-r) ≤ ‖F.correlation a j‖) :
    Real.exp (-r) ≤
      ‖((F.chart a).slice.fullSliceLaw
        ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
        (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
          F.nativeValue j (F.physicalBox a u)) * (F.localTest a j).eval u.val)‖ := by
  have hm := (F.chart a).localLaw_complexMean_eq_fullSliceLaw_site (fun site =>
    star ((F.twist a j).eval N poly (F.sitePhysicalBox a site).val) *
      ((F.reference a j).observable ((F.sourceCandidate a).siteValue site) *
        F.nativeValue j (F.sitePhysicalBox a site)))
  rw [F.chart_localLaw] at hm
  unfold correlation at hcorr
  rw [hm] at hcorr
  convert hcorr using 2
  congr 1
  funext u
  have hv : (F.sourceCandidate a).siteValue ((F.chart a).site u.val u.property) =
      (F.candidate a).value u.val := by
    rw [← (F.sourceCandidate a).withKeep_siteValue keep (F.keep_eq a)]
    change (F.candidate a).value
      ((F.chart a).retainedParameter ((F.chart a).parameter u.val)) = _
    rw [(F.chart a).retainedParameter_parameter]
  simp only [localTest, hv]
  change (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      F.nativeValue j (F.physicalBox a u)) *
      (F.reference a j).observable ((F.candidate a).value u.val) =
    star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      ((F.reference a j).observable ((F.candidate a).value u.val) *
        F.nativeValue j (F.physicalBox a u))
  ring

theorem selectedCorrelation_localLaw
    (V : ∀ j, (F.native j).model.Niltest (fullTaggedVariableWeight (X := X) J))
    (a : Ω) (j : Pivot)
    (hcorr : Real.exp (-p) ≤
      ‖((F.chart a).slice.fullSliceLaw
        ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
        star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
          ((F.localTest a j).eval u.val *
            (V j).eval (fullTaggedPhysicalIntegerPoint J poly
              (fun k => ((F.chart a).centerLift k).val) (F.physicalBox a u).val)))‖) :
    Real.exp (-p) ≤ ‖(F.sourceChart a).localLaw.complexMean (fun site =>
      star ((F.twist a j).eval N poly (A.physical (F.sourceChart a).path site)) *
        ((F.reference a j).observable
            ((F.candidate a).value ((F.chart a).retainedParameter site.val)) *
          (V j).eval (fullTaggedPhysicalIntegerPoint J poly
            (fun k => ((F.sourceChart a).centerLift k).val)
            (A.physical (F.sourceChart a).path site))))‖ := by
  have hm := (F.chart a).localLaw_complexMean_eq_fullSliceLaw_site (fun site =>
    star ((F.twist a j).eval N poly (A.physical (F.sourceChart a).path site)) *
      ((F.reference a j).observable
          ((F.candidate a).value ((F.chart a).retainedParameter site.val)) *
        (V j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => ((F.sourceChart a).centerLift k).val)
          (A.physical (F.sourceChart a).path site))))
  rw [F.chart_localLaw] at hm
  rw [hm]
  convert hcorr using 2
  congr 1
  funext u
  change star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
      ((F.reference a j).observable
          ((F.candidate a).value ((F.chart a).retainedParameter ((F.chart a).parameter u.val))) *
        (V j).eval (fullTaggedPhysicalIntegerPoint J poly
          (fun k => ((F.chart a).centerLift k).val) (F.physicalBox a u).val)) = _
  rw [(F.chart a).retainedParameter_parameter]
  rfl

theorem exp_correlation_bound {q : ℝ}
    (hbudget : r + verticalDecompositionBudget q + 2 ≤ p) :
    Real.exp (-p) ≤ Real.exp (-r) / (2 * Real.exp (verticalDecompositionBudget q)) := by
  apply (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans
  apply (le_div_iff₀ (by positivity)).mpr
  have he : Real.exp (-(r + verticalDecompositionBudget q + 2)) *
      (2 * Real.exp (verticalDecompositionBudget q)) = 2 * Real.exp (-r - 2) := by
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  calc
    _ ≤ Real.exp 2 * Real.exp (-r - 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_pos _).le
    _ = Real.exp (-r) := by rw [← Real.exp_add]; congr 1; ring

theorem exists_taggedPairFamily [Fintype Ω]
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    {q : ℝ} (hpq : pNative ≤ q) (hprecision : pLocal + r + 1 ≤ q)
    (hfrequency : verticalDecompositionBudget q ≤ p)
    (hbudget : r + verticalDecompositionBudget q + 2 ≤ p)
    (hcorr : ∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) :
    ∃ (retained : Finset Ω),
      retained ⊆ H ∧ 0 < outer.mass retained ∧
      Real.exp (-verticalDecompositionBudget q * Fintype.card Pivot) * outer.mass H ≤
        outer.mass retained ∧
      ∃ selectedFamily : AllocatedExternalCandidateTaggedPairFamily A Deck
          {a // a ∈ retained} Pivot D (fun j => (F.native j).model) Fmark φ marked
          keep cost p periodCap coverCap Lip,
        (∀ a, selectedFamily.sourceChart a = F.sourceChart a.val) ∧
        (∀ a, HEq (selectedFamily.sourceCandidate a) (F.sourceCandidate a.val)) ∧
        selectedFamily.reference = (fun a => F.reference a.val) ∧
        selectedFamily.twist = (fun a => F.twist a.val) ∧
        selectedFamily.η = F.η ∧
        (∀ j, selectedFamily.ambient j = (F.native j).test.fullTaggedSpatial J) ∧
        ∀ a, selectedFamily.jointOrbit a = F.jointOrbit a.val := by
  classical
  have hfull (a : Ω) (ha : a ∈ H) (j : Pivot) :
      Real.exp (-r) ≤
        ‖((F.chart a).slice.fullSliceLaw
          ((F.chart a).slice.length_pos_of_dense (F.chart a).dense)).complexMean (fun u =>
          (star ((F.twist a j).eval N poly (F.physicalBox a u).val) *
            F.nativeValue j (F.physicalBox a u)) * (F.localTest a j).eval u.val)‖ := by
    exact F.rawCorrelation_fullSliceLaw a j (hcorr a ha j)
  obtain ⟨freq, V, retained, hsub, hpos, hmass, hcert, hheight, hvert, hselected⟩ :=
    exists_spatialNative_slice_tagged_vertical_partners
      (Ω := Ω) (Pivot := Pivot) (K := {i // keep i})
      (N := fun i : {i // keep i} => A.sides i.val)
      (pNative := pNative) (pLocal := pLocal) (r := r) (q := q) J poly D
      (fun x : integerBox N => x.val) F.nativeValue F.native F.localTest outer H hH
      (fun a _ => (F.chart a).step) (fun a _ => (F.chart a).slice)
      (fun a _ _ => (F.chart a).step_pos)
      (fun a _ i => (F.chart a).slice.length_pos_of_dense (F.chart a).dense i)
      F.physicalBox (fun a k => ((F.chart a).centerLift k).val)
      (fun a j u => (F.twist a j).eval N poly (F.physicalBox a u).val)
      F.hpLocal F.hr hpq hprecision
      (fun a _ j => F.hV a j)
      (fun a _ j u => (F.twist a j).norm_eval_le N poly _) hfull
  let selectedFamily : AllocatedExternalCandidateTaggedPairFamily A Deck
      {a // a ∈ retained} Pivot D (fun j => (F.native j).model) Fmark φ marked
      keep cost p periodCap coverCap Lip := {
    hpoly := F.hpoly
    hτ1 := F.hτ1
    hξ := F.hξ
    hσ1 := F.hσ1
    Cgeo := F.Cgeo
    hCgeo := F.hCgeo
    hchart := F.hchart
    hsmall := F.hsmall
    sourceChart := fun a => F.sourceChart a.val
    keep_eq := fun a => F.keep_eq a.val
    sourceCandidate := fun a => F.sourceCandidate a.val
    reference := fun a => F.reference a.val
    ambient := fun j => (F.native j).test.fullTaggedSpatial J
    selected := V
    selected_orbit := fun j => (hcert j).1
    twist := fun a => F.twist a.val
    hp := F.hp
    hcost := F.hcost
    hperiod := fun a => F.hperiod a.val
    hvariation := F.hvariation
    hV := fun a j => (F.hV a.val j).mono F.hlocal
    hW := fun j => (hcert j).2.1.mono F.hnative
    hWnorm := fun j => (hcert j).2.2
    η := F.η
    θ := freq
    hηheight := F.hηheight
    hθheight := fun j i => (hheight j i).trans hfrequency
    hη := fun a => F.hη a.val
    hθ := hvert
    hK := F.hK
    hcorr := by
      intro a j
      exact F.selectedCorrelation_localLaw V a.val j
        ((exp_correlation_bound hbudget).trans (hselected a.val a.property j)) }
  exact ⟨retained, hsub, hpos, hmass, selectedFamily,
    (fun _ => rfl), (fun _ => HEq.rfl), rfl, rfl, rfl, (fun _ => rfl), (fun _ => rfl)⟩

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {Ω Freq Bin : Type} [Fintype Ω] [Fintype Bin] [Nonempty Bin]
    {LG LM : Type} [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d t rank : ℕ} (D : RationalFilteredNilmanifold LG s d)
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {cost : ℝ} (C : Ω → AllocatedExternalLocalChart (E := Deck) A cost)
    (candidate : ∀ a, AllocatedExternalLocalCandidate (C a) D Fmark φ marked)
    (hξ1 : ξ ≤ 1)

theorem exists_precenter_spatial_native_family
    (external : Freq → integerBox N → D.Niltest (fullTaggedVariableWeight (X := X) J))
    (representative : Bin → integerBox N)
    (eta : Freq → LG →ₗ[ℚ] ℚ)
    {p pLocal pNative r inputBound ε δ coefficientBound termBound residualBound : ℝ}
    (hcomplex : ∀ f x, (external f x).ComplexityLE pLocal)
    (hnet : ∀ f x, ∃ i, ∀ y, ‖(external f x).observable y -
      (external f (representative i)).observable y‖ ≤ ε)
    (input : integerBox N → ℂ)
    (models : (Freq × Bin) → CenteredForecastModel (integerBox N))
    (periodCap coverCap : ℝ) (Lip : ℝ≥0)
    {Y Forecast : Type} [MeasurableSpace Y]
    (jointLaw : Measure Y) (referenceLaw : FiniteProbabilityWeights (integerBox N))
    (forecast : Forecast → integerBox N → ℂ)
    (localSeminorm : (integerBox N → ℂ) → ℝ)
    (selectedLocal : (integerBox N → ℂ) → (Y → ℂ) → Prop)
    (hmodels : ∀ branch, CenteredForecastModelBounds jointLaw
      (twistedNativeSampleFunctions (fun _ : X => 1) s pNative
        (fun x : integerBox N => x.val)
        (fun (twist : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
          (x : integerBox N) => twist.eval N poly x.val))
      referenceLaw forecast localSeminorm selectedLocal
      (externalNetMaskFamily (fun f x => (external f x).observable)
        (fun f i => (external f (representative i)).observable) hnet input branch)
      coefficientBound residualBound termBound (models branch))
    (hM : 0 < coefficientBound) (hterm : 1 ≤ termBound)
    (code : Fin rank → Option Freq)
    (outer : FiniteProbabilityWeights Ω) (H : Finset Ω) (hH : 0 < outer.mass H)
    (hB : 0 ≤ inputBound) (hδ : 0 < δ) (herror : inputBound * ε ≤ δ / 2)
    (hinput : ∀ x, ‖input x‖ ≤ inputBound)
    {Eres sliceBudget testBudget : ℝ}
    (hcost0 : 0 ≤ cost)
    (hshort : ∀ a ∈ H, ∀ i : {i // ¬(C a).keep i},
      (A.sides i.val : ℝ) ≤ Real.exp cost)
    (hSliceBudget : cost ≤ sliceBudget) (hTestBudget : pLocal ≤ testBudget)
    (hUniform : ∀ a ∈ H, ∀ f i,
      ∀ packet : UniversalLocalMajorSliceTest A.sides s sliceBudget testBudget,
        ‖𝔼 site ∈ packet.slice.subtypeSites,
          (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
            packet.weight site.val‖ ≤ Real.exp (-Eres))
    (hresBudget : Real.exp (pLocal - Eres) ≤ (δ / (2 * Fintype.card Bin)) / 2)
    (hscore : ∀ a ∈ H, ∀ i f, code i = some f → δ ≤
      ‖(C a).localLaw.complexMean (fun site =>
        input (A.boxedPhysical hξ1 (C a).path site) *
          (external f (A.boxedPhysical hξ1 (C a).path site)).observable
            ((candidate a).siteValue site))‖)
    (hcorrBudget : Real.exp (-r) ≤ (δ / (2 * Fintype.card Bin)) / (2 * coefficientBound))
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ a, (C a).keep = keep)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hτ1 : τ ≤ 1) (hσ1 : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : 0 ≤ p) (hpLocal : 0 ≤ pLocal) (hr : 0 ≤ r)
    (hcost : cost ≤ p) (hlocal : pLocal ≤ p) (hnative : pNative ≤ p)
    (hperiod : periodCap * coverCap ≤ Real.exp p)
    (hvariation : (Lip : ℝ) * (1 + (m : ℝ) * (((m + 1 : ℕ) : ℝ) *
      ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m)) ≤ Real.exp p)
    (hetaHeight : ∀ f i, rationalLogHeight (eta f (D.basis i)) ≤ p)
    (hvertical : ∀ f x z, z ∈ D.filtration.realification.subgroup s → ∀ y,
      (external f x).observable (z • y) = CircleFourier.character
        ((realifyFunctional (eta f) z.coord : ℝ) : CircleFourier.Circle) *
          (external f x).observable y)
    (hK : (Fintype.card {i // keep i} : ℝ) ≤ p) :
    ∃ (retained : Finset Ω), retained ⊆ H ∧ 0 < outer.mass retained ∧
      outer.mass H / ((Fintype.card Bin : ℝ) ^ rank * termBound ^ rank) ≤ outer.mass retained ∧
      ∃ F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω
          (KernelProjectionPresentPivot code) D Fmark φ marked keep cost p pLocal pNative r
          periodCap coverCap Lip,
        F.sourceChart = C ∧ (∀ a, HEq (F.sourceCandidate a) (candidate a)) ∧
        F.η = (fun k => eta (kernelProjectionSelectedPivot code k)) ∧
        ∀ a ∈ retained, ∀ k, Real.exp (-r) ≤ ‖F.correlation a k‖ := by
  have hresidual : ∀ a ∈ H, ∀ f i,
      ‖(C a).localLaw.complexMean (fun site =>
        (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site) *
          (external f (representative i)).observable ((candidate a).siteValue site))‖ ≤
            (δ / (2 * Fintype.card Bin)) / 2 := by
    intro a ha f i
    exact ((candidate a).localLaw_residual_le_exp_of_universal_native_budget
      (external f (representative i)) (hcomplex f _) hcost0 (hshort a ha)
      hSliceBudget hTestBudget
      (fun site => (models (f, i)).residual (A.boxedPhysical hξ1 (C a).path site))
      (hUniform a ha f i)).trans hresBudget
  obtain ⟨chosen, twist, value, native, retained, hsub, hpos, hmass, _, hcorr⟩ :=
    A.exists_precenter_native_partners D C candidate hξ1 external representative hcomplex hnet
      input models s pNative periodCap coverCap Lip jointLaw referenceLaw forecast localSeminorm
      selectedLocal hmodels hM hterm code outer H hH hB hδ herror hinput hresidual hscore
  let F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω
      (KernelProjectionPresentPivot code) D Fmark φ marked keep cost p pLocal pNative r
      periodCap coverCap Lip := {
    hpoly := hpoly
    hτ1 := hτ1
    hξ := hξ1
    hσ1 := hσ1
    Cgeo := Cgeo
    hCgeo := hCgeo
    hchart := hchart
    hsmall := hsmall
    sourceChart := C
    keep_eq := hkeep
    sourceCandidate := candidate
    reference := fun _ k => external (kernelProjectionSelectedPivot code k) (representative (chosen k))
    nativeValue := value
    native := native
    twist := fun _ => twist
    hp := hp
    hpLocal := hpLocal
    hr := hr
    hcost := hcost
    hlocal := hlocal
    hnative := hnative
    hperiod := by
      intro a k
      rw [Nat.cast_mul]
      exact (mul_le_mul (twist k).modulus_bound (twist k).cover_bound
        (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans (twist k).modulus_bound)).trans hperiod
    hvariation := hvariation
    hV := fun _ k => hcomplex _ _
    η := fun k => eta (kernelProjectionSelectedPivot code k)
    hηheight := fun k i => hetaHeight _ i
    hη := fun _ k => hvertical _ _
    hK := hK }
  refine ⟨retained, hsub, hpos, hmass, F, rfl, (fun _ => HEq.rfl), rfl, ?_⟩
  intro a ha k
  apply hcorrBudget.trans
  simpa only [AllocatedExternalCandidateSpatialNativeFamily.correlation,
    AllocatedExternalCandidateSpatialNativeFamily.sitePhysicalBox, F, boxedPhysical, mul_assoc]
    using hcorr a ha k

end AllocatedExternalCandidateSampler
end
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {A} {Deck : Fin m → Type*} {Ω Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ t : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM t} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

def withBudget (q : ℝ) (hpq : p ≤ q) :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost q pLocal pNative r periodCap coverCap Lip where
  hpoly := F.hpoly
  hτ1 := F.hτ1
  hξ := F.hξ
  hσ1 := F.hσ1
  Cgeo := F.Cgeo
  hCgeo := F.hCgeo
  hchart := F.hchart
  hsmall := F.hsmall
  sourceChart := F.sourceChart
  keep_eq := F.keep_eq
  sourceCandidate := F.sourceCandidate
  reference := F.reference
  nativeValue := F.nativeValue
  native := F.native
  twist := F.twist
  hp := F.hp.trans hpq
  hpLocal := F.hpLocal
  hr := F.hr
  hcost := F.hcost.trans hpq
  hlocal := F.hlocal.trans hpq
  hnative := F.hnative.trans hpq
  hperiod := fun a j => (F.hperiod a j).trans (Real.exp_le_exp.mpr hpq)
  hvariation := F.hvariation.trans (Real.exp_le_exp.mpr hpq)
  hV := F.hV
  η := F.η
  hηheight := fun j i => (F.hηheight j i).trans hpq
  hη := F.hη
  hK := F.hK.trans hpq

@[simp] theorem withBudget_sourceChart (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).sourceChart = F.sourceChart := rfl

@[simp] theorem withBudget_sourceCandidate (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withBudget_reference (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).reference = F.reference := rfl

@[simp] theorem withBudget_nativeValue (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).nativeValue = F.nativeValue := rfl

@[simp] theorem withBudget_native (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).native = F.native := rfl

@[simp] theorem withBudget_twist (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).twist = F.twist := rfl

@[simp] theorem withBudget_eta (q : ℝ) (hpq : p ≤ q) :
    (F.withBudget q hpq).η = F.η := rfl

@[simp] theorem withBudget_chart (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).chart a = F.chart a := rfl

@[simp] theorem withBudget_candidate (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).candidate a = F.candidate a := rfl

@[simp] theorem withBudget_jointOrbit (q : ℝ) (hpq : p ≤ q) (a : Ω) :
    (F.withBudget q hpq).jointOrbit a = F.jointOrbit a := rfl

@[simp] theorem withBudget_correlation (q : ℝ) (hpq : p ≤ q) (a : Ω) (j : Pivot) :
    (F.withBudget q hpq).correlation a j = F.correlation a j := rfl

def withFactorBudget :
    AllocatedExternalCandidateSpatialNativeFamily A Deck Ω Pivot D Fmark φ marked
      keep cost (spatialNativeFactorParameter p pNative pLocal r)
      pLocal pNative r periodCap coverCap Lip :=
  F.withBudget (spatialNativeFactorParameter p pNative pLocal r) (le_max_left _ _)

@[simp] theorem withFactorBudget_sourceChart :
    F.withFactorBudget.sourceChart = F.sourceChart := rfl

@[simp] theorem withFactorBudget_sourceCandidate :
    F.withFactorBudget.sourceCandidate = F.sourceCandidate := rfl

@[simp] theorem withFactorBudget_native : F.withFactorBudget.native = F.native := rfl

@[simp] theorem withFactorBudget_twist : F.withFactorBudget.twist = F.twist := rfl

@[simp] theorem withFactorBudget_eta : F.withFactorBudget.η = F.η := rfl

@[simp] theorem withFactorBudget_correlation (a : Ω) (j : Pivot) :
    F.withFactorBudget.correlation a j = F.correlation a j := rfl

include F in

theorem factorBudget_bounds :
    pNative ≤ spatialNativeVerticalParameter pNative pLocal r ∧
    pLocal + r + 1 ≤ spatialNativeVerticalParameter pNative pLocal r ∧
    verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) ≤
      spatialNativeFactorParameter p pNative pLocal r ∧
    r + verticalDecompositionBudget (spatialNativeVerticalParameter pNative pLocal r) + 2 ≤
      spatialNativeFactorParameter p pNative pLocal r := by
  obtain ⟨_, hnative, hprecision, _, _, hfrequency, hbudget⟩ :=
    spatialNativeVerticalFactorBounds p pNative pLocal r F.hpLocal F.hr
  exact ⟨hnative, hprecision, hfrequency, hbudget⟩

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI
