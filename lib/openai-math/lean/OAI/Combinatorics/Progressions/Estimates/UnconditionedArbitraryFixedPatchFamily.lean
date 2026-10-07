/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
import OAI.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
import OAI.Combinatorics.Progressions.Sampling.FixedPatchShearFiberCandidateScore

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal

theorem exists_relative_finite_returned_slice_normalization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {Ω J : Type*}
      [Fintype Ω] [Nonempty Ω] [Fintype J] [DecidableEq J]
      (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω),
      0 < outer.mass productive →
      ∀ (P : J → ℕ), (∀ i, 0 < P i) →
      ∀ (p : ℝ), 0 ≤ p → ∀ (Λ : ℝ), Λ ∈ Set.Icc (0 : ℝ) 1 →
      ∀ (d₀ : ℕ) (f : Ω → (J → ℤ) → ℝ),
      (∀ h x, x ∈ integerBox P → f h x ∈ Set.Icc (0 : ℝ) 1) →
      (∀ h ∈ productive, RelativePatchSliceConclusion s P (f h) Λ d₀ p) →
      let q := p + (Fintype.card J : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (localLaw : Ω → FiniteProbabilityWeights (integerBox P))
        (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots J d w) (localForm : Ω → PolynomialSlots J d w)
        (retained : Finset Ω),
        d ≤ D ∧ d ≤ d₀ ∧ (∀ i, 1 ≤ w i) ∧ (∀ i, w i ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ i, realPolynomialMass (B.center i) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (outer.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ outer.mass retained ∧
        (∀ h ∈ retained, ∃ r, 0 < r ∧ ∃ (S : ResidueBoxSlice P r)
          (hlen : ∀ i, 0 < S.length i),
          (∀ i, Real.exp (-p) * (P i : ℝ) ≤ (S.length i : ℝ)) ∧
            localLaw h = S.fullSliceLaw hlen) ∧
        ∀ h ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw h).mean
          (fun x => (f h x.val - Λ) * (B.shearTransformedSlots hw
            ((localForm h).loweringAt (fun i => (x.val i : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_varying_rank_fixed_patch_function s
  refine ⟨E, hE, ?_⟩
  intro Ω J _ _ _ _ outer productive hmass P hP p hp Λ hΛ d₀ f hf hreturn
  let q := p + (Fintype.card J : ℝ) + 2
  let D := min d₀ ⌊p⌋₊
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  obtain ⟨h₀, hh₀⟩ := hne
  obtain ⟨ddefault, Qdefault, lawdefault, hddefault, _, hlipdefault, _, _⟩ :=
    (hreturn h₀ hh₀).tighten_rank.exists_full_law hP
  have hall (h : Ω) : ∃ (d : ℕ) (Q : PolynomialPatch J s d)
      (localLaw : FiniteProbabilityWeights (integerBox P)),
      d ≤ D ∧ (Q.kernel.lip : ℝ) ≤ Real.exp p ∧
      (h ∈ productive → Real.exp (-p) ≤ localLaw.mean
        (fun x => (f h x.val - Λ) * Q.value (fun i => (x.val i : ℝ)))) ∧
      (h ∈ productive → ∃ r, 0 < r ∧ ∃ (S : ResidueBoxSlice P r)
        (hlen : ∀ i, 0 < S.length i),
        (∀ i, Real.exp (-p) * (P i : ℝ) ≤ (S.length i : ℝ)) ∧
          localLaw = S.fullSliceLaw hlen) := by
    by_cases hh : h ∈ productive
    · obtain ⟨d, Q, localLaw, hd, _, hlip, hscore, hslice⟩ :=
        (hreturn h hh).tighten_rank.exists_full_law hP
      exact ⟨d, Q, localLaw, hd, hlip, fun _ => hscore, fun _ => hslice⟩
    · exact ⟨ddefault, Qdefault, lawdefault, hddefault, hlipdefault,
        fun hmem => (hh hmem).elim, fun hmem => (hh hmem).elim⟩
  choose d patch localLaw hd hlip hpositive hslice using hall
  have hpq : p ≤ q := by
    dsimp only [q]
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
  have hq : 0 ≤ q := hp.trans hpq
  have hD : (D : ℝ) ≤ q :=
    (Nat.cast_le.mpr (Nat.min_le_right d₀ ⌊p⌋₊)).trans ((Nat.floor_le hp).trans hpq)
  have hJ : (Fintype.card J : ℝ) ≤ q := by dsimp only [q]; linarith
  have hLip (h) : ((patch h).kernel.lip : ℝ) ≤ Real.exp q :=
    (hlip h).trans (Real.exp_le_exp.mpr hpq)
  let point := fun (_ : Ω) (x : integerBox P) => x.val
  let score := fun h (x : integerBox P) => f h x.val - Λ
  have hscore (h) (x : integerBox P) : |score h x| ≤ 1 := by
    dsimp only [score]
    obtain ⟨hf0, hf1⟩ := hf h x.val x.property
    exact abs_le.mpr ⟨by linarith [hΛ.2], by linarith [hΛ.1]⟩
  have hpositive' (h) (hh : h ∈ productive) : Real.exp (-q) ≤ (localLaw h).mean
      (fun x => score h x * (patch h).value (fun i => (point h x i : ℝ))) :=
    (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hpositive h hh)
  obtain ⟨d', w, hw, Ψ, B, localForm, retained, hd', hpos, hws, hΨ, hB,
      hsub, hmass', hlocal⟩ :=
    hfixed outer productive d patch D q hd hmass hq hD hJ hLip
      localLaw point score hscore hpositive'
  exact ⟨localLaw, d', w, hw, Ψ, B, localForm, retained, hd',
    hd'.trans (Nat.min_le_left _ _), hpos, hws, hΨ, hB, hsub, hmass',
    fun h hh => hslice h (hsub hh), hlocal⟩

end Erdos3

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

structure AllocatedReturnedPatchSource (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j) (z : A.Path) where
  supported : 0 < A.law.weight z
  sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n
  read : AllocatedActualCoefficientIndex G X I E n B → ℤ
  recovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
    centerLift z.1.val z.2.val sample read
  fixed : {i // ¬keep i} → ℤ
  fixed_in_box : ∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val

namespace AllocatedReturnedPatchSource

variable {keep : LayerSamplerVariables G I n B → Prop} {centerLift : ∀ j, U j}
    {z : A.Path} (source : AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z)

noncomputable def physical (u : {i // keep i} → ℤ) : X → ℤ :=
  jointIntegerPhysicalSite (finiteSplitPoint keep u source.fixed) (z.1.val, z.2.val)

noncomputable def chart {cost : ℝ}
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    {q : ℕ} (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < slice.length i)
    (hlength : ∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i) :
    AllocatedExternalLocalChart (E := E) A cost where
  path := z
  path_supported := source.supported
  centerLift := centerLift
  center_eq := hcenter
  sample := source.sample
  read := source.read
  recovered := source.recovered
  keep := keep
  fixed := source.fixed
  fixed_in_box := source.fixed_in_box
  step := q
  step_pos := hq
  slice := slice
  dense := ⟨_, _, _, hq, hlen, slice.progression_inside, hlength,
    slice.integerPoints_eq_commonStrideBox⟩

@[simp] theorem chart_physical {cost : ℝ}
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    {q : ℕ} (slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q)
    (hq : 0 < q) (hlen : ∀ i, 0 < slice.length i)
    (hlength : ∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i)
    (u : {i // keep i} → ℤ) :
    (source.chart hcenter slice hq hlen hlength).physical u = source.physical u := rfl

end AllocatedReturnedPatchSource

noncomputable def allocatedNormalizedShearProblem
    {Y : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch Y s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots {i // keep i} d patch.weight)
    (q : productive → ℕ) (hq : ∀ z, 0 < q z)
    (slice : ∀ z, ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) (q z))
    (hlen : ∀ z i, 0 < (slice z).length i)
    (hlength : ∀ z i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ (slice z).length i)
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ ((slice z).fullSliceLaw (hlen z)).mean
      (fun u => (f ((source z).physical u.val) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold where
  productive := productive
  mass := hmass
  chart z := (source z).chart hcenter (slice z) (hq z) (hlen z) (hlength z)
  chart_path _ := rfl
  centerLift := centerLift
  chart_centerLift _ := rfl
  frozen_side _ := hshort
  candidate z := {
    orbit := (localForm z).shearPolynomialOrbit s patch.weight_le
    mark_on_slice := by
      intro u hu
      apply NilpotentLieBCHGroup.ext
      exact Subsingleton.elim _ _ }
  score z := by
    have hs := hscore z
    rw [patch.fullSliceLaw_shearObservable_score (localForm z) (slice z)
      (hq z) (hlen z) (fun u => f ((source z).physical u)) lam] at hs
    exact hs

theorem exists_allocatedNormalizedShearProblem_of_returned_laws
    {Y : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch Y s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots {i // keep i} d patch.weight)
    (law : ∀ _ : productive,
      FiniteProbabilityWeights (integerBox (fun i : {i // keep i} => A.sides i.val)))
    (hslice : ∀ z, ∃ q, 0 < q ∧
      ∃ slice : ResidueBoxSlice (fun i : {i // keep i} => A.sides i.val) q,
      ∃ hlen : ∀ i, 0 < slice.length i,
        (∀ i, Real.exp (-cost) * (A.sides i.val : ℝ) ≤ slice.length i) ∧
          law z = slice.fullSliceLaw hlen)
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ (law z).mean
      (fun u => (f ((source z).physical u.val) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    Nonempty (AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold) := by
  choose q hq slice hlen hlength hlaw using hslice
  refine ⟨allocatedNormalizedShearProblem keep centerLift hcenter productive hmass
    source hshort patch localForm q hq slice hlen hlength f lam ?_⟩
  intro z
  simpa only [← hlaw z] using hscore z

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

theorem exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
    {V : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : productive → AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        centerLift z.val.1.val z.val.2.val (sample z) (read z))
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : productive → PolynomialSlots (LayerSamplerVariables G I n B) d patch.weight)
    (law : productive → FiniteProbabilityWeights A.Site)
    (hslice : ∀ z, RelativeReturnedFiberLaw keep A.sides cost (law z))
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z, scoreThreshold ≤ (law z).mean
      (fun u => (f (A.physical z.val u) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    ∃ P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold,
      P.productive = productive ∧ P.centerLift = centerLift ∧
        ∀ z, (P.chart z).keep = keep := by
  have hcert := hslice
  unfold RelativeReturnedFiberLaw at hcert
  choose fixed hfixed q hq slice hlen hlength hlaw using hcert
  let source : ∀ z : productive,
      AllocatedReturnedPatchSource (E := E) (A := A) keep centerLift z.val := fun z =>
    ⟨hsupported z, sample z, read z, hread z, fixed z, hfixed z⟩
  let keptForm := fun z => (localForm z).coordinateFiberForm keep (fixed z)
  have hkeptScore (z : productive) : scoreThreshold ≤
      ((slice z).fullSliceLaw (hlen z)).mean (fun u =>
        (f ((source z).physical u.val) - lam) *
          (patch.form.shearTransformedSlots patch.weight_mono
            ((keptForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel) := by
    have hs := hscore z
    rw [hlaw z] at hs
    dsimp only [AllocatedExternalCandidateSampler.physical] at hs
    rw [patch.fiberSliceLaw_shear_score_eq_fullSliceLaw (localForm z) keep
      (slice z) (hlen z) (fixed z) (hfixed z)
      (fun u => f (jointIntegerPhysicalSite u (z.val.1.val, z.val.2.val))) lam] at hs
    have hdec :
        (fun a b : {i // keep i} => Classical.propDecidable (a = b)) =
        (fun a b => @Subtype.instDecidableEq _ keep
          (inferInstance : DecidableEq (LayerSamplerVariables G I n B)) a b) :=
      Subsingleton.elim _ _
    rw [← hdec] at hs
    simpa only [keptForm, AllocatedReturnedPatchSource.physical, source] using hs
  let P := allocatedNormalizedShearProblem keep centerLift hcenter productive hmass
    source hshort patch keptForm q hq slice hlen hlength f lam hkeptScore
  exact ⟨P, rfl, rfl, fun _ => rfl⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem exists_allocatedFixedCenterNormalizedShearProblem
    (s : ℕ) (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j)
    (hcenter : coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun a => centerLift a.1))))
    (productive : Finset A.Path) (hmass : 0 < A.law.mass productive)
    (hsupported : ∀ z : productive, 0 < A.law.weight z.val)
    (sample : productive → CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : productive → AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hread : ∀ z : productive,
      AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
        centerLift z.val.1.val z.val.2.val (sample z) (read z))
    (p cost : ℝ) (hp : 0 ≤ p) (hpcost : p ≤ cost)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (rankBound : ℕ) (f : (X → ℤ) → ℝ) (target : ℝ)
    (htarget : target ∈ Set.Icc (0 : ℝ) 1)
    (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) (hξ1 : ξ ≤ 1)
    (hreturned : ∀ z ∈ productive, ∃ (fixed : {i // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i < (A.sides i.val : ℤ)) ∧
      RelativePatchSliceConclusion s (fun i : {i // keep i} => A.sides i.val)
        (fun u => f (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed)
          (z.1.val, z.2.val))) target rankBound p) :
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let q := p + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    let D := min rankBound ⌊p⌋₊
    let normalizedBudget := (q + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = keep := by
  intro normalizationPower q D normalizedBudget retainedMass
  have hne : productive.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty] at hmass
    linarith)
  let : Nonempty A.Path := hne.to_subtype.map Subtype.val
  let pathInput := fun (z : A.Path) (u : LayerSamplerVariables G I n B → ℤ) =>
    f (jointIntegerPhysicalSite u (z.1.val, z.2.val))
  have hinput : ∀ z u, u ∈ integerBox A.sides → pathInput z u ∈ Set.Icc (0 : ℝ) 1 := by
    intro z u hu
    exact hf _ (A.physical_mem_integerBox hξ1 z ⟨u, hu⟩)
  obtain ⟨localLaw, d, w, hw, Ψ, slots, localForm, retained,
      hd, hdrank, hwpos, hwle, hLip, hslots, hsub, hretained, hslice, hscore⟩ :=
    (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose_spec.2
      A.law productive hmass A.sides keep A.sides_pos p hp target htarget rankBound
      pathInput hinput hreturned
  let patch : PolynomialPatch (LayerSamplerVariables G I n B) s d :=
    ⟨w, hwpos, hwle, hw, slots, Ψ⟩
  let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
  obtain ⟨P, hP, hcenterP, hkeep⟩ :=
    exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
      (E := E) (A := A) keep centerLift hcenter retained hretained
      (fun z => hsupported ⟨z.val, hsub z.property⟩)
      (fun z => sample ⟨z.val, hsub z.property⟩)
      (fun z => read ⟨z.val, hsub z.property⟩)
      (fun z => hread ⟨z.val, hsub z.property⟩)
      hshort patch (fun z => localForm z.val) (fun z => localLaw z.val)
      (fun z => (hslice z.val z.property).mono hpcost) f target
      (fun z => hscore z.val z.property)
  exact ⟨d, patch, hd, hdrank, hLip, hslots, P, hP ▸ hsub, hcenterP, hkeep⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
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

theorem exists_allocatedZeroLayerNormalizedShearProblem
    {V : Type*} {s d : ℕ} (keep : LayerSamplerVariables G I n B → Prop)
    (productive : Finset A.Path) {massThreshold cost scoreThreshold : ℝ}
    (hmass : massThreshold ≤ A.law.mass productive)
    (hshort : ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    (localForm : A.Path → PolynomialSlots (LayerSamplerVariables G I n B) d patch.weight)
    (law : A.Path → FiniteProbabilityWeights A.Site)
    (hslice : ∀ z ∈ productive, RelativeReturnedFiberLaw keep A.sides cost (law z))
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hscore : ∀ z ∈ productive, scoreThreshold ≤ (law z).mean
      (fun u => (f (A.physical z u) - lam) *
        (patch.form.shearTransformedSlots patch.weight_mono
          ((localForm z).loweringAt (fun i => (u.val i : ℝ)))).patchValue patch.kernel)) :
    ∃ P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold,
      P.productive ⊆ productive ∧ A.law.mass P.productive = A.law.mass productive ∧
        P.centerLift = allocatedZeroLayerCenterLift U ∧
        ∀ z, (P.chart z).keep = keep := by
  let supported := productive.filter (fun z => 0 < A.law.weight z)
  have hsub : supported ⊆ productive := Finset.filter_subset _ _
  have hsame : A.law.mass supported = A.law.mass productive := by
    unfold FiniteProbabilityWeights.mass
    dsimp only [supported]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro z _
    by_cases hz : 0 < A.law.weight z
    · rw [ite_eq_left hz]
    · rw [ite_eq_right hz]
      exact (le_antisymm (le_of_not_gt hz) (A.law.nonneg z)).symm
  obtain ⟨P, hP, hcenter, hkeep⟩ :=
    exists_allocatedNormalizedShearProblem_of_returned_fiber_laws
      (E := E) (A := A) keep (allocatedZeroLayerCenterLift U)
      (allocatedZeroLayerCenterLift_spec B U center) supported
      (hmass.trans_eq hsame.symm)
      (fun z => (Finset.mem_filter.mp z.property).2)
      (fun _ => allocatedZeroLayerSample B)
      (fun z => allocatedZeroLayerFramedRead (E := E) B z.val.1.val z.val.2.val)
      (fun z => allocatedZeroLayer_recovered B U b hb o S hR hσ poly hm
        z.val.1.val z.val.2.val)
      hshort patch (fun z => localForm z.val) (fun z => law z.val)
      (fun z => hslice z.val (hsub z.property)) f lam
      (fun z => hscore z.val (hsub z.property))
  exact ⟨P, hP ▸ hsub, hP ▸ hsame, hcenter, hkeep⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

def AllocatedNormalizedCandidateConclusion
    (s : ℕ) (keep : LayerSamplerVariables G I n B → Prop)
    (centerLift : ∀ j, U j) (productive : Finset A.Path)
    (childCost cost : ℝ) (rankBound : ℕ) (f : (X → ℤ) → ℝ) (target : ℝ) : Prop :=
    let normalizationPower := (exists_relative_finite_returned_fiber_normalization.{0,0} s).choose
    let q := childCost + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    let D := min rankBound ⌊childCost⌋₊
    let normalizedBudget := (q + 2) ^ normalizationPower
    let retainedMass := (A.law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
      Real.exp (-normalizedBudget)
    ∃ (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
      d ≤ D ∧ d ≤ rankBound ∧
      (patch.kernel.lip : ℝ) ≤ Real.exp normalizedBudget ∧
      (∀ i, realPolynomialMass (patch.form.center i) ≤ normalizedBudget) ∧
      let := polynomialShearIndexFintype patch.weight (fun i => patch.weight_pos i)
      ∃ P : AllocatedExternalCandidateProblem (E := E) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - target : ℝ) : ℂ)) cost retainedMass (Real.exp (-normalizedBudget)),
        P.productive ⊆ productive ∧ P.centerLift = centerLift ∧
          ∀ z, (P.chart z).keep = keep

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

namespace BooleanCubeKernel

theorem exists_unconditioned_arbitrary_fixed_patch_family (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (n₀ : ℕ) {X : Type*} [Fintype X] [DecidableEq X]
      (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)] (_i : X)
      {p a Λ σ : ℝ}, 0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 → 0 < σ → σ ≤ 1 →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ k, (P k).Prime) → Function.Injective P →
      (∀ k j, P k ≤ 2 ^ (n₀ + 1) * P j) →
      (∀ k, Real.exp p ≤ (P k : ℝ)) →
      ∀ (N : X → ℕ),
        (∀ j, unconditionedSpatialWidthCutoff (unconditionedResidueSiteBound P)
          (unconditionedSpatialTrimFraction (Fintype.card X) σ)
          (unconditionedCollisionWidth P σ) ≤ (N j : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        a + σ ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
      let R := spatialTrimMargin τ N
      let q := p + (n₀ : ℝ) + 2
      let D := min d₀ ⌊p⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ (productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ k, ZMod (P k) =>
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1, ∀ u : ∀ k, ZMod (P k),
          jointIntegerPhysicalSite (residueBoxIntegerPoint P u) (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots (Fin n₀) d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots (Fin n₀) d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox P))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ d₀ ∧ d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ m, 0 < m ∧ ∃ (S : ResidueBoxSlice P m)
          (hlen : ∀ j, 0 < S.length j),
          (∀ j, Real.exp (-p) * (P j : ℝ) ≤ (S.length j : ℝ)) ∧
          localLaw z = S.fullSliceLaw hlen) ∧
        ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_relative_finite_returned_slice_normalization s
  refine ⟨E, hE, ?_⟩
  intro n₀ X _ _ P _ i p a Λ σ hp ha hΛ hσ hσ1 d₀ habsolute hprime hdistinct
    hcomparable hcutoff N hN f hf hfree hmean
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := Fin n₀) (unconditionedResidueSiteBound P) τ N
  let R := spatialTrimMargin τ N
  let q := p + (n₀ : ℝ) + 2
  let D := min d₀ ⌊p⌋₊
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hreturn, hinside⟩ :=
    exists_unconditioned_arbitrary_absolute_family s n₀ P i ha hσ hσ1 d₀ habsolute
      hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  let law := selectedJointReference (trimmedIntegerBox N R)
    (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
  have hprod : 0 < law.mass productive := (div_pos hσ (by norm_num)).trans_le hmass
  have hnonempty : productive.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    simp only [he, FiniteProbabilityWeights.mass, Finset.sum_empty, lt_self_iff_false] at hprod
  obtain ⟨z₀, _⟩ := hnonempty
  let : Nonempty (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) := ⟨z₀⟩
  have hbound (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)
      (x : Fin n₀ → ℤ) (hx : x ∈ integerBox P) :
      f (jointIntegerPhysicalSite x (z.1.val,z.2.val)) ∈ Set.Icc (0 : ℝ) 1 := by
    have hrep : residueBoxIntegerPoint P (fun j => (x j : ZMod (P j))) = x := by
      funext j
      have hxj := (mem_integerBox P x).mp hx j
      dsimp only [residueBoxIntegerPoint]
      rw [ZMod.val_intCast, Int.emod_eq_of_lt hxj.1 hxj.2]
    have hi := hinside z (fun j => (x j : ZMod (P j)))
    rw [hrep] at hi
    exact hf _ hi
  obtain ⟨localLaw, d, w, hw, Ψ, B, localForm, retained, hd, hd₀, hpos, hws, hΨ, hB,
      hsub, hretained, hcertificate, hlocal⟩ :=
    hfixed law productive hprod P (fun j => (hprime j).pos) p hp Λ hΛ d₀
      (fun z x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) hbound hreturn
  refine ⟨hW, hR, hZ, productive, hmass, hinj, hinside, d, w, hw, Ψ, B,
    localForm, localLaw, retained, hd₀, hd, hpos, hws,
    ?_, ?_, hsub, ?_, ?_, hcertificate, ?_⟩
  · simpa only [Fintype.card_fin] using hΨ
  · simpa only [Fintype.card_fin] using hB
  · simpa only [Fintype.card_fin] using hretained
  · have hle := mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hmass (by positivity : (0 : ℝ) ≤ ((D + 1) * (s + 1) ^ D : ℕ)))
      (Real.exp_nonneg (-((q + 2) ^ E)))
    exact hle.trans (by simpa only [Fintype.card_fin] using hretained)
  · simpa only [Fintype.card_fin] using hlocal

end BooleanCubeKernel
end Erdos3

end

end OAI
