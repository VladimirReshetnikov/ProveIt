/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.NativePairChartSymbol
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalLocalSliceLaw

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
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

def keptInclusion (i : {i // keep i}) : C.Variables := ⟨i.val, hkeep i.val i.property⟩

noncomputable def axisSlice : ResidueBoxSlice
    (fun i : {i // keep i} => A.sides i.val) C.step :=
  C.slice.comap (C.keptInclusion keep hkeep)

variable (fixed : {i : C.Variables // ¬keep i.val} → ℤ)

noncomputable def axisPoint (u : {i // keep i} → ℤ) : C.Variables → ℤ :=
  fun i => if hi : keep i.val then u ⟨i.val, hi⟩ else fixed ⟨i, hi⟩

noncomputable def axisFixed : {i // ¬keep i} → ℤ :=
  fun i => if hi : C.keep i.val then fixed ⟨⟨i.val, hi⟩, i.property⟩ else C.fixed ⟨i.val, hi⟩

variable (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
    (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable abbrev freezeAxes : AllocatedExternalLocalChart (E := E) A (max cost shortCost) where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := keep
  fixed := C.axisFixed keep fixed
  fixed_in_box i := by
    dsimp only [axisFixed]
    split_ifs with hi
    · exact Finset.mem_Ico.mp (C.slice.progression_inside ⟨i.val, hi⟩ (hfixed ⟨⟨i.val, hi⟩, i.property⟩))
    · exact C.fixed_in_box ⟨i.val, hi⟩
  step := C.step
  step_pos := C.step_pos
  slice := C.axisSlice keep hkeep
  dense := (C.slice.comap_isDenseCommonStrideBox C.step_pos C.dense
    (C.keptInclusion keep hkeep)).mono (le_max_left _ _)

@[simp] theorem freezeAxes_path :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).path = C.path := rfl

@[simp] theorem freezeAxes_centerLift :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).centerLift = C.centerLift := rfl

theorem freezeAxes_parameter (u : {i // keep i} → ℤ) :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).parameter u =
      C.parameter (C.axisPoint keep fixed u) := by
  funext i
  by_cases hk : keep i
  · have hc := hkeep i hk
    simp [parameter, freezeAxes, axisPoint, finiteSplitPoint, hk, hc]
  · by_cases hc : C.keep i
    · simp [parameter, axisFixed, axisPoint, finiteSplitPoint, hk, hc]
    · simp [parameter, axisFixed, finiteSplitPoint, hk, hc]

theorem freezeAxes_physical (u : {i // keep i} → ℤ) :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).physical u =
      C.physical (C.axisPoint keep fixed u) := by
  unfold physical
  rw [C.freezeAxes_parameter keep hkeep fixed hfixed]

theorem freezeAxes_chartValues (u : {i // keep i} → ℤ) :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).chartValues u =
      C.chartValues (C.axisPoint keep fixed u) := by
  funext i
  change MvPolynomial.eval u (freezePolynomial keep (C.axisFixed keep fixed) _) =
    MvPolynomial.eval (C.axisPoint keep fixed u) (freezePolynomial C.keep C.fixed _)
  rw [freezePolynomial_eval, freezePolynomial_eval]
  apply congrArg (fun x => MvPolynomial.eval x _)
  exact C.freezeAxes_parameter (shortCost := shortCost) keep hkeep fixed hfixed u

noncomputable def axisPolynomial (i : C.Variables) : MvPolynomial {i // keep i} ℝ :=
  if hi : keep i.val then MvPolynomial.X ⟨i.val, hi⟩ else MvPolynomial.C (fixed ⟨i, hi⟩ : ℝ)

theorem axisPolynomial_support (i : C.Variables) :
    C.axisPolynomial keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i.val
  · rw [axisPolynomial, dite_eq_left hi]
    exact weightedSupportLE_X (R := ℝ) (fun _ : {i // keep i} => 1) ⟨i.val, hi⟩
  · rw [axisPolynomial, dite_eq_right hi]
    exact weightedSupportLE_C (fun _ : {i // keep i} => 1) 1 (fixed ⟨i, hi⟩ : ℝ)

theorem axisPolynomial_eval (u : {i // keep i} → ℤ) (i : C.Variables) :
    MvPolynomial.eval (fun k => (u k : ℝ)) (C.axisPolynomial keep fixed i) =
      (C.axisPoint keep fixed u i : ℝ) := by
  by_cases hi : keep i.val <;> simp [axisPolynomial, axisPoint, hi]

include hfixed in

theorem axisPoint_mem {u : {i // keep i} → ℤ}
    (hu : u ∈ (C.axisSlice keep hkeep).integerPoints) :
    C.axisPoint keep fixed u ∈ C.slice.integerPoints := by
  apply (C.slice.mem_integerPoints_iff _).mpr
  have hu' := ((C.axisSlice keep hkeep).mem_integerPoints_iff _).mp hu
  intro i
  by_cases hi : keep i.val
  · simpa only [axisPoint, dite_eq_left hi, axisSlice, ResidueBoxSlice.comap, keptInclusion] using hu' ⟨i.val, hi⟩
  · simpa only [axisPoint, dite_eq_right hi] using hfixed ⟨i, hi⟩

def axisCoordinateEquiv : ({i // keep i} → ℤ) ≃
    ({i : C.Variables // keep i.val} → ℤ) where
  toFun u i := u ⟨i.val.val, i.property⟩
  invFun v i := v ⟨C.keptInclusion keep hkeep i, i.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem axisSlice_expect (f : (C.Variables → ℤ) → ℝ) :
    (𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints, f (C.axisPoint keep fixed u)) =
      𝔼 u ∈ (C.slice.coordinateProjection (fun i : C.Variables => keep i.val)).integerPoints,
        f (finiteSplitPoint (fun i : C.Variables => keep i.val) u fixed) := by
  apply Finset.expect_equiv (C.axisCoordinateEquiv keep hkeep)
  · intro u
    rw [ResidueBoxSlice.mem_integerPoints_iff, ResidueBoxSlice.mem_integerPoints_iff]
    constructor
    · intro hu i
      exact hu ⟨i.val.val, i.property⟩
    · intro hu i
      exact hu ⟨C.keptInclusion keep hkeep i, i.property⟩
  · intro u _
    rfl

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable def axisOrbit : D.filtration.realification.PolynomialOrbit
    (fun _ : {i // keep i} => 1) :=
  D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
    (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit

theorem axisOrbit_eval (u : {i // keep i} → ℤ) :
    D.filtration.realification.polynomialOrbitEval (fun _ => 1) u
      (candidate.axisOrbit keep fixed) =
      D.filtration.realification.polynomialOrbitEval (fun _ => 1)
        (C.axisPoint keep fixed u) candidate.orbit := by
  simpa only [axisOrbit, C.axisPolynomial_eval, polynomialOrbitRealEval_integer] using
    D.filtration.polynomialOrbitRealChart_realEval (fun _ => 1) (fun _ => 1)
      (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
      candidate.orbit (fun i => (u i : ℝ))

noncomputable def freezeAxes : AllocatedExternalLocalCandidate
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed) D Fmark φ marked where
  orbit := candidate.axisOrbit keep fixed
  mark_on_slice u hu := by
    rw [candidate.axisOrbit_eval, C.freezeAxes_chartValues]
    exact candidate.mark_on_slice _ (C.axisPoint_mem keep hkeep fixed hfixed hu)

theorem freezeAxes_value (u : {i // keep i} → ℤ) :
    (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).value u =
      candidate.value (C.axisPoint keep fixed u) := by
  change QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ => 1) u (candidate.axisOrbit keep fixed)) = _
  rw [candidate.axisOrbit_eval]
  rfl

theorem freezeAxes_score (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ) :
    (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).score observable weight =
      𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints,
        (weight (C.physical (C.axisPoint keep fixed u)) *
          observable (C.physical (C.axisPoint keep fixed u))
            (candidate.value (C.axisPoint keep fixed u))).re := by
  simp only [score, C.freezeAxes_physical, candidate.freezeAxes_value, Complex.re_expect]

noncomputable def freezeAxesScore (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) : ℝ :=
  (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).score observable weight

theorem exists_freezeAxes (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) {a : ℝ} (hscore : a ≤ candidate.score observable weight) :
    ∃ fixed : {i : C.Variables // ¬keep i.val} → ℤ,
      (∀ i, fixed i ∈ integerProgressionSupport
        (C.slice.start i.val : ℤ) C.step (C.slice.length i.val)) ∧
      a ≤ 𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints,
        (weight (C.physical (C.axisPoint keep fixed u)) *
          observable (C.physical (C.axisPoint keep fixed u))
            (candidate.value (C.axisPoint keep fixed u))).re := by
  let f : (C.Variables → ℤ) → ℝ := fun u =>
    (weight (C.physical u) * observable (C.physical u) (candidate.value u)).re
  have hmean : a ≤ 𝔼 u ∈ C.slice.integerPoints, f u := by
    simpa only [score, Complex.re_expect] using hscore
  obtain ⟨fixed, hfixed, _, hmean'⟩ := C.slice.exists_coordinate_fiber_score C.step_pos
    (C.slice.length_pos_of_dense C.dense) (fun i : C.Variables => keep i.val) f hmean
  refine ⟨fixed, hfixed, ?_⟩
  exact (C.axisSlice_expect keep hkeep fixed f).symm ▸ hmean'

end AllocatedExternalLocalCandidate

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] polynomialOrbitRealChart
  integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable abbrev restrictAxes : AllocatedExternalLocalChart (E := E) A cost where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := keep
  fixed := C.axisFixed keep fixed
  fixed_in_box := (C.freezeAxes (shortCost := cost) keep hkeep fixed hfixed).fixed_in_box
  step := C.step
  step_pos := C.step_pos
  slice := C.axisSlice keep hkeep
  dense := C.slice.comap_isDenseCommonStrideBox C.step_pos C.dense
    (C.keptInclusion keep hkeep)

@[simp] theorem restrictAxes_path :
    (C.restrictAxes keep hkeep fixed hfixed).path = C.path := rfl

@[simp] theorem restrictAxes_centerLift :
    (C.restrictAxes keep hkeep fixed hfixed).centerLift = C.centerLift := rfl

theorem restrictAxes_parameter (u : {i // keep i} → ℤ) :
    (C.restrictAxes keep hkeep fixed hfixed).parameter u =
      C.parameter (C.axisPoint keep fixed u) :=
  C.freezeAxes_parameter (shortCost := cost) keep hkeep fixed hfixed u

theorem restrictAxes_physical (u : {i // keep i} → ℤ) :
    (C.restrictAxes keep hkeep fixed hfixed).physical u =
      C.physical (C.axisPoint keep fixed u) :=
  C.freezeAxes_physical (shortCost := cost) keep hkeep fixed hfixed u

theorem restrictAxes_chartValues (u : {i // keep i} → ℤ) :
    (C.restrictAxes keep hkeep fixed hfixed).chartValues u =
      C.chartValues (C.axisPoint keep fixed u) :=
  C.freezeAxes_chartValues (shortCost := cost) keep hkeep fixed hfixed u

theorem axisSlice_complexMean (f : (C.Variables → ℤ) → ℂ) :
    (𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints, f (C.axisPoint keep fixed u)) =
      𝔼 u ∈ (C.slice.coordinateProjection (fun i : C.Variables => keep i.val)).integerPoints,
        f (finiteSplitPoint (fun i : C.Variables => keep i.val) u fixed) := by
  apply Finset.expect_equiv (C.axisCoordinateEquiv keep hkeep)
  · intro u
    rw [ResidueBoxSlice.mem_integerPoints_iff, ResidueBoxSlice.mem_integerPoints_iff]
    constructor
    · intro hu i
      exact hu ⟨i.val.val, i.property⟩
    · intro hu i
      exact hu ⟨C.keptInclusion keep hkeep i, i.property⟩
  · intro u _
    rfl

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable def restrictAxes : AllocatedExternalLocalCandidate
    (C.restrictAxes keep hkeep fixed hfixed) D Fmark φ marked where
  orbit := candidate.axisOrbit keep fixed
  mark_on_slice u hu := by
    rw [candidate.axisOrbit_eval, C.restrictAxes_chartValues]
    exact candidate.mark_on_slice _ (C.axisPoint_mem keep hkeep fixed hfixed hu)

theorem restrictAxes_value (u : {i // keep i} → ℤ) :
    (candidate.restrictAxes keep hkeep fixed hfixed).value u =
      candidate.value (C.axisPoint keep fixed u) := by
  change QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval (fun _ => 1) u
    (candidate.axisOrbit keep fixed)) = _
  rw [candidate.axisOrbit_eval]
  rfl

theorem localLaw_complexMean_parameter_value
    (test : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ) :
    C.localLaw.complexMean (fun site => test site.val (candidate.siteValue site)) =
      𝔼 u ∈ C.slice.integerPoints, test (C.parameter u) (candidate.value u) := by
  simpa only [siteValue, C.retainedParameter_parameter] using
    C.localLaw_complexMean_parameter
      (fun x => test x (candidate.value (C.retainedParameter x)))

theorem restrictAxes_complexMean
    (test : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ) :
    (C.restrictAxes keep hkeep fixed hfixed).localLaw.complexMean (fun site =>
      test site.val ((candidate.restrictAxes keep hkeep fixed hfixed).siteValue site)) =
      𝔼 u ∈ (C.axisSlice keep hkeep).integerPoints,
        test (C.parameter (C.axisPoint keep fixed u))
          (candidate.value (C.axisPoint keep fixed u)) := by
  rw [(candidate.restrictAxes keep hkeep fixed hfixed).localLaw_complexMean_parameter_value]
  simp only [restrictAxes_value, C.restrictAxes_parameter]

theorem exists_restrictAxes_norm
    (test : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ) :
    ∃ fixed : {i : C.Variables // ¬keep i.val} → ℤ,
      ∃ hfixed : ∀ i : {i : C.Variables // ¬keep i.val}, fixed i ∈ integerProgressionSupport
        (C.slice.start i.val : ℤ) C.step (C.slice.length i.val),
      ‖C.localLaw.complexMean (fun site => test site.val (candidate.siteValue site))‖ ≤
        ‖(C.restrictAxes keep hkeep fixed hfixed).localLaw.complexMean (fun site =>
          test site.val ((candidate.restrictAxes keep hkeep fixed hfixed).siteValue site))‖ := by
  let f : (C.Variables → ℤ) → ℂ :=
    fun u => test (C.parameter u) (candidate.value u)
  obtain ⟨fixed, hfixed, _, hnorm⟩ := C.slice.exists_coordinate_fiber_norm C.step_pos
    (C.slice.length_pos_of_dense C.dense) (fun i : C.Variables => keep i.val) f
  refine ⟨fixed, hfixed, ?_⟩
  rw [candidate.localLaw_complexMean_parameter_value,
    candidate.restrictAxes_complexMean keep hkeep fixed hfixed,
    C.axisSlice_complexMean keep hkeep fixed f]
  exact hnorm

theorem exists_restrictAxes_site_norm (test : A.Site → D.Space → ℂ) :
    ∃ fixed : {i : C.Variables // ¬keep i.val} → ℤ,
      ∃ hfixed : ∀ i : {i : C.Variables // ¬keep i.val}, fixed i ∈ integerProgressionSupport
        (C.slice.start i.val : ℤ) C.step (C.slice.length i.val),
      ‖C.localLaw.complexMean (fun site => test site (candidate.siteValue site))‖ ≤
        ‖(C.restrictAxes keep hkeep fixed hfixed).localLaw.complexMean (fun site =>
          test site ((candidate.restrictAxes keep hkeep fixed hfixed).siteValue site))‖ := by
  let extension : (LayerSamplerVariables G I n B → ℤ) → D.Space → ℂ :=
    fun x y => if hx : x ∈ integerBox A.sides then test ⟨x, hx⟩ y else 0
  obtain ⟨fixed, hfixed, hnorm⟩ := candidate.exists_restrictAxes_norm keep hkeep extension
  refine ⟨fixed, hfixed, ?_⟩
  have he (site : A.Site) (y : D.Space) : extension site.val y = test site y := by
    simp only [extension, dite_eq_left site.property]
  simpa only [he] using hnorm

end AllocatedExternalLocalCandidate

end Erdos3.VectorPolynomial

end

section

universe u

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct

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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {cost : ℝ}

namespace AllocatedExternalLocalChart

variable (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed fixed' : {i : C.Variables // ¬keep i.val} → ℤ)

theorem axisPolynomial_top_independent (i : C.Variables) :
    weightedHomogeneousComponent (fun _ : {i // keep i} => 1) 1
      (C.axisPolynomial keep fixed i) =
    weightedHomogeneousComponent (fun _ : {i // keep i} => 1) 1
      (C.axisPolynomial keep fixed' i) := by
  by_cases hi : keep i.val
  · simp only [axisPolynomial, dite_eq_left hi]
  · simp only [axisPolynomial, dite_eq_right hi]
    rw [(isWeightedHomogeneous_C (fun _ : {i // keep i} => 1)
      (fixed ⟨i, hi⟩ : ℝ)).weightedHomogeneousComponent_ne 1 (by decide),
      (isWeightedHomogeneous_C (fun _ : {i // keep i} => 1)
      (fixed' ⟨i, hi⟩ : ℝ)).weightedHomogeneousComponent_ne 1 (by decide)]

end AllocatedExternalLocalChart

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d e : ℕ}
    {C : AllocatedExternalLocalChart (E := Deck) A cost}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)

namespace AllocatedExternalLocalChart

theorem pairOrbitSymbol_axisPolynomial_independent
    (C : AllocatedExternalLocalChart (E := Deck) A cost)
    (p : D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    (q : E.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed fixed' : {i : C.Variables // ¬keep i.val} → ℤ)
    {ι : Type*} (pairBasis : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (pairBasis '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) p)
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) q)
      pairBasis ω hF =
    pairOrbitSymbol D E
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed') p)
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed') q)
      pairBasis ω hF := by
  apply pairOrbitSymbol_chart_eq_of_homogeneous_eq D E p q pairBasis ω hF
    (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
    (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed')
  funext i
  exact C.axisPolynomial_top_independent keep fixed fixed' i

end AllocatedExternalLocalChart

namespace AllocatedExternalLocalCandidate

variable {D} {Target : Type*} [LieRing Target] [LieAlgebra ℚ Target] {t : ℕ}
    {Fmark : NilpotentLieFiltration Target t} {φ : L →ₗ⁅ℚ⁆ Target}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

theorem pairOrbitSymbol_axisOrbit_independent
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (fixed fixed' : {i : C.Variables // ¬keep i.val} → ℤ)
    (partnerOrbit : E.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))
    {ι : Type*} (pairBasis : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (pairBasis '' {i | k ≤ ω i})) :
    pairOrbitSymbol D E (candidate.axisOrbit keep fixed)
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) partnerOrbit)
      pairBasis ω hF =
    pairOrbitSymbol D E (candidate.axisOrbit keep fixed')
      (E.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed') (C.axisPolynomial_support keep fixed') partnerOrbit)
      pairBasis ω hF :=
  C.pairOrbitSymbol_axisPolynomial_independent D E candidate.orbit partnerOrbit
    keep fixed fixed' pairBasis ω hF

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure AxisFreezing
    (keep : P.productive → LayerSamplerVariables G I n B → Prop) (shortCost : ℝ) where
  keep_subset : ∀ z i, keep z i → (P.chart z).keep i
  removed_side : ∀ z (i : (P.chart z).Variables),
    ¬keep z i.val → (A.sides i.val : ℝ) ≤ Real.exp shortCost
  fixed : ∀ z, {i : (P.chart z).Variables // ¬keep z i.val} → ℤ
  fixed_mem : ∀ z i, fixed z i ∈ integerProgressionSupport
    ((P.chart z).slice.start i.val : ℤ) (P.chart z).step ((P.chart z).slice.length i.val)
  score_mono : ∀ z, (P.candidate z).score observable weight ≤
    (P.candidate z).freezeAxesScore (shortCost := shortCost) (keep z) (keep_subset z)
      (fixed z) (fixed_mem z) observable weight

namespace AxisFreezing

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

noncomputable abbrev problem :
    AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      (max cost shortCost) massThreshold scoreThreshold where
  productive := P.productive
  mass := P.mass
  chart z := (P.chart z).freezeAxes (shortCost := shortCost) (keep z)
    (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
  chart_path := P.chart_path
  centerLift := P.centerLift
  chart_centerLift := P.chart_centerLift
  frozen_side z i := by
    by_cases hi : (P.chart z).keep i.val
    · exact (freezing.removed_side z ⟨i.val, hi⟩ i.property).trans
        (Real.exp_le_exp.mpr (le_max_right _ _))
    · exact (P.frozen_side z ⟨i.val, hi⟩).trans
        (Real.exp_le_exp.mpr (le_max_left _ _))
  candidate z := (P.candidate z).freezeAxes (shortCost := shortCost) (keep z)
    (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
  score z := by
    change scoreThreshold ≤ (P.candidate z).freezeAxesScore (shortCost := shortCost)
      (keep z) (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
      observable weight
    exact (P.score z).trans (freezing.score_mono z)

@[simp] theorem problem_productive : freezing.problem.productive = P.productive := rfl

@[simp] theorem problem_centerLift : freezing.problem.centerLift = P.centerLift := rfl

@[simp] theorem problem_chart (z : P.productive) :
    freezing.problem.chart z = (P.chart z).freezeAxes (shortCost := shortCost) (keep z)
      (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z) := rfl

@[simp] theorem problem_chart_keep (z : P.productive) :
    (freezing.problem.chart z).keep = keep z := rfl

theorem problem_slice_dense (z : P.productive) :
    IsDenseCommonStrideBox
      (fun i : (freezing.problem.chart z).Variables => A.sides i.val) cost
      (freezing.problem.chart z).slice.integerPoints :=
  (P.chart z).slice.comap_isDenseCommonStrideBox (P.chart z).step_pos (P.chart z).dense
    ((P.chart z).keptInclusion (keep z) (freezing.keep_subset z))

@[simp] theorem problem_slice_length (z : P.productive)
    (i : (freezing.problem.chart z).Variables) :
    (freezing.problem.chart z).slice.length i =
      (P.chart z).slice.length
        ((P.chart z).keptInclusion (keep z) (freezing.keep_subset z) i) := rfl

theorem problem_slice_length_lower (z : P.productive)
    (i : (freezing.problem.chart z).Variables) :
    Real.exp (-cost) * (A.sides i.val : ℝ) ≤
      ((freezing.problem.chart z).slice.length i : ℝ) :=
  (P.chart z).slice.length_lower_of_dense (P.chart z).step_pos (P.chart z).dense
    ((P.chart z).keptInclusion (keep z) (freezing.keep_subset z) i)

@[simp] theorem problem_candidate (z : P.productive) :
    freezing.problem.candidate z = (P.candidate z).freezeAxes (shortCost := shortCost) (keep z)
      (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z) := rfl

theorem problem_score_mono (z : P.productive) :
    (P.candidate z).score observable weight ≤
      (freezing.problem.candidate z).score observable weight :=
  freezing.score_mono z

theorem problem_slice_inside (z : P.productive)
    {u : {i // keep z i} → ℤ}
    (hu : u ∈ (freezing.problem.chart z).slice.integerPoints) :
    (P.chart z).axisPoint (keep z) (freezing.fixed z) u ∈
      (P.chart z).slice.integerPoints :=
  (P.chart z).axisPoint_mem (keep z) (freezing.keep_subset z)
    (freezing.fixed z) (freezing.fixed_mem z) hu

end AxisFreezing

theorem exists_axisFreezing
    (keep : P.productive → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z i, keep z i → (P.chart z).keep i) (shortCost : ℝ)
    (hremoved : ∀ z (i : (P.chart z).Variables),
      ¬keep z i.val → (A.sides i.val : ℝ) ≤ Real.exp shortCost) :
    Nonempty (P.AxisFreezing keep shortCost) := by
  have hex (z : P.productive) :=
    (P.candidate z).exists_freezeAxes (keep z) (hkeep z)
      observable weight (a := (P.candidate z).score observable weight) le_rfl
  choose fixed hfixed hscore using hex
  exact ⟨{ keep_subset := hkeep
           removed_side := hremoved
           fixed := fixed
           fixed_mem := hfixed
           score_mono := fun z => by
             rw [AllocatedExternalLocalCandidate.freezeAxesScore,
               AllocatedExternalLocalCandidate.freezeAxes_score]
             exact hscore z }⟩

def thresholdKeep (H : ℕ) (z : P.productive) (i : LayerSamplerVariables G I n B) : Prop :=
  (P.chart z).keep i ∧ H ≤ A.sides i

theorem exists_thresholdAxisFreezing (H : ℕ) :
    Nonempty (P.AxisFreezing (P.thresholdKeep H) (Real.log ((max H 1 : ℕ) : ℝ))) := by
  apply P.exists_axisFreezing (P.thresholdKeep H) (fun _ _ hi => hi.1)
  intro z i hi
  have hlt : A.sides i.val < H := by
    have hnot : ¬ H ≤ A.sides i.val := fun h => hi ⟨i.property, h⟩
    exact Nat.lt_of_not_ge hnot
  have hpos : (0 : ℝ) < ((max H 1 : ℕ) : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (le_max_right H 1))
  rw [Real.exp_log hpos]
  exact_mod_cast (hlt.le.trans (le_max_left H 1))

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem ResidueBoxSlice.integerPoints_classical_eq {V : Type*} [Finite V]
    {N : V → ℕ} {q : ℕ} (t : Fintype V) (d : DecidableEq V) (slice : ResidueBoxSlice N q) :
    @ResidueBoxSlice.integerPoints V N q t d slice =
      @ResidueBoxSlice.integerPoints V N q (Fintype.ofFinite V) (Classical.decEq V) slice := by
  cases Subsingleton.elim t (Fintype.ofFinite V)
  cases Subsingleton.elim d (Classical.decEq V)
  rfl

theorem isDenseCommonStrideBox_classical_iff {V : Type*} [Finite V]
    (t : Fintype V) (d : DecidableEq V) (N : V → ℕ) (cost : ℝ) (points : Finset (V → ℤ)) :
    @IsDenseCommonStrideBox V t d N cost points ↔
      @IsDenseCommonStrideBox V (Fintype.ofFinite V) (Classical.decEq V) N cost points := by
  cases Subsingleton.elim t (Fintype.ofFinite V)
  cases Subsingleton.elim d (Classical.decEq V)
  rfl

end Erdos3

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

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
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

namespace AxisFreezing

variable {P} {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

noncomputable def extendSlice (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step) :
    ResidueBoxSlice (fun i : (P.chart z).Variables => A.sides i.val) step :=
  slice.extendAxes (N := A.sides) (oldKeep := (P.chart z).keep) (keep := keep z) (P.chart z).slice (freezing.fixed z) (freezing.fixed_mem z)

theorem ambientScore_extendSlice
    (ambient : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step) :
    P.ambientScore ambient z (freezing.extendSlice z slice).integerPoints =
      freezing.problem.ambientScore ambient z slice.integerPoints := by
  let f : ((P.chart z).Variables → ℤ) → ℂ := fun u =>
    weight ((P.chart z).physical u) * observable ((P.chart z).physical u)
      (QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval
        (fullTaggedVariableWeight J) ((P.chart z).chartValues u) ambient))
  have hexpect := slice.expect_extendAxes (N := A.sides)
    (oldKeep := (P.chart z).keep) (keep := keep z)
    (P.chart z).slice (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z) f
  have haxis : ResidueBoxSlice.axisInsertion (P.chart z).keep (keep z) (freezing.fixed z) =
      (P.chart z).axisPoint (keep z) (freezing.fixed z) := rfl
  rw [haxis] at hexpect
  calc
    _ = (𝔼 u ∈ slice.integerPoints,
        f ((P.chart z).axisPoint (keep z) (freezing.fixed z) u)).re :=
      congrArg Complex.re (by
        simpa only [ResidueBoxSlice.integerPoints_classical_eq, extendSlice, f] using hexpect)
    _ = _ := by
      unfold ambientScore
      dsimp only [problem]
      simp only [AllocatedExternalLocalChart.freezeAxes_physical,
        AllocatedExternalLocalChart.freezeAxes_chartValues]
      rfl

theorem extendSlice_dense (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step)
    (hstep : 0 < step) {outputCost : ℝ}
    (hdense : IsDenseCommonStrideBox (fun i : {i // keep z i} => A.sides i.val)
      outputCost slice.integerPoints) :
    IsDenseCommonStrideBox (fun i : (P.chart z).Variables => A.sides i.val)
      (max outputCost shortCost) (freezing.extendSlice z slice).integerPoints :=
by
  have h := slice.extendAxes_dense (N := A.sides)
    (oldKeep := (P.chart z).keep) (keep := keep z)
    (P.chart z).slice (freezing.fixed z) (freezing.fixed_mem z) hstep
    (outCost := outputCost) (by
      simpa only [isDenseCommonStrideBox_classical_iff,
        ResidueBoxSlice.integerPoints_classical_eq] using hdense)
    (freezing.removed_side z)
  simpa only [isDenseCommonStrideBox_classical_iff,
    ResidueBoxSlice.integerPoints_classical_eq, extendSlice] using h

theorem extendSlice_inside (z : P.productive) {step : ℕ}
    (slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) step)
    (hinside : slice.integerPoints ⊆ (freezing.problem.chart z).slice.integerPoints) :
    (freezing.extendSlice z slice).integerPoints ⊆ (P.chart z).slice.integerPoints :=
by
  intro x hx
  have hx' : x ∈ (slice.extendAxes (N := A.sides)
      (oldKeep := (P.chart z).keep) (keep := keep z)
      (P.chart z).slice (freezing.fixed z) (freezing.fixed_mem z)).integerPoints := by
    simpa only [ResidueBoxSlice.integerPoints_classical_eq, extendSlice] using hx
  have haxis : ResidueBoxSlice.axisInsertion (P.chart z).keep (keep z) (freezing.fixed z) =
      (P.chart z).axisPoint (keep z) (freezing.fixed z) := rfl
  have himage := slice.extendAxes_integerPoints (N := A.sides)
    (oldKeep := (P.chart z).keep) (keep := keep z)
    (P.chart z).slice (freezing.keep_subset z) (freezing.fixed z) (freezing.fixed_mem z)
  simp only [ResidueBoxSlice.integerPoints_classical_eq, haxis] at himage
  simp only [ResidueBoxSlice.integerPoints_classical_eq] at hx'
  rw [himage] at hx'
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx'
  apply freezing.problem_slice_inside z
  apply hinside
  simpa only [ResidueBoxSlice.integerPoints_classical_eq] using hu

theorem conclusion_subset {outputCost outputMass outputScore : ℝ}
    (out : freezing.problem.Conclusion outputCost outputMass outputScore) :
    out.retained ⊆ P.productive := out.subset

noncomputable def conclusion {outputCost outputMass outputScore : ℝ}
    (out : freezing.problem.Conclusion outputCost outputMass outputScore) :
    P.Conclusion (max outputCost shortCost) outputMass outputScore where
  ambient := out.ambient
  marked := out.marked
  retained := out.retained
  subset := freezing.conclusion_subset out
  mass := out.mass
  step := out.step
  step_pos := out.step_pos
  slice z := freezing.extendSlice ⟨z.val, freezing.conclusion_subset out z.property⟩ (out.slice z)
  dense z := freezing.extendSlice_dense ⟨z.val, freezing.conclusion_subset out z.property⟩
    (out.slice z) (out.step_pos z) (out.dense z)
  inside z := freezing.extendSlice_inside ⟨z.val, freezing.conclusion_subset out z.property⟩
    (out.slice z) (out.inside z)
  score z := (out.score z).trans_eq
    (freezing.ambientScore_extendSlice out.ambient
      ⟨z.val, freezing.conclusion_subset out z.property⟩ (out.slice z)).symm

end AxisFreezing
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
