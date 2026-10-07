import OAI.Combinatorics.Progressions.Dynamics.UnconditionedRootBudgetAbsoluteFamily
import OAI.Combinatorics.Progressions.Estimates.UnconditionedArbitraryFixedPatchFamily
import OAI.Combinatorics.Progressions.Geometry.UnconditionedCommonSideSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllKeptSliceLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical NNReal

theorem exists_unconditioned_commonSide_fixed_patch_family (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (n₀ : ℕ) {K X : Type*}
      [Fintype K] [DecidableEq K] [Fintype X] [DecidableEq X]
      (P : Fin n₀ → ℕ) [∀ k, NeZero (P k)] (e : K ≃ Fin n₀)
    (S : ℕ), 0 < S → ∀ (_i : X) {p a Λ σ extra : ℝ},
      0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 → 0 < σ → σ ≤ 1 →
      0 ≤ extra → (∀ j, P j ≤ S) →
      (∀ j, (S : ℝ) ≤ Real.exp extra * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
        (∀ j, unconditionedSpatialWidthCutoff ((Fintype.card K : ℝ) * S)
          (unconditionedSpatialTrimFraction (Fintype.card X) σ)
          (unconditionedCollisionWidth P σ) ≤ (N j : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ), (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        a + σ ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
      let W := trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N
      let R := spatialTrimMargin τ N
      let q := p + extra + (Fintype.card K : ℝ) + 2
      let D := min d₀ ⌊p + extra⌋₊
      ∃ (hW : ∀ z, 0 < W z) (hR : ∀ j, 2 * R j < N j)
        (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z),
      let law := selectedJointReference (trimmedIntegerBox N R)
        (trimmedIntegerBox_nonempty N R hR) (fun _ : X => 1) {0} W hW hZ
      ∃ productive : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1),
        σ / 4 ≤ law.mass productive ∧
        (∀ z ∈ productive, Function.Injective (fun u : ∀ j, ZMod (P j) =>
          jointIntegerPhysicalSite (fun k => residueBoxIntegerPoint P u (e k))
            (z.1.val,z.2.val))) ∧
        (∀ z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1,
          ∀ x ∈ integerBox (fun _ : K => S),
          jointIntegerPhysicalSite x (z.1.val,z.2.val) ∈ integerBox N) ∧
      ∃ (d : ℕ) (w : Fin d → ℕ) (hw : Monotone w) (Ψ : PatchKernel d)
        (B : PolynomialSlots K d w)
        (localForm : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          PolynomialSlots K d w)
        (localLaw : (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1) →
          FiniteProbabilityWeights (integerBox (fun _ : K => S)))
        (retained : Finset (trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)),
        d ≤ d₀ ∧ d ≤ D ∧ (∀ j, 1 ≤ w j) ∧ (∀ j, w j ≤ s) ∧
        (Ψ.lip : ℝ) ≤ Real.exp ((q + 2) ^ E) ∧
        (∀ j, realPolynomialMass (B.center j) ≤ (q + 2) ^ E) ∧
        retained ⊆ productive ∧
        (law.mass productive / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        ((σ / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
          Real.exp (-((q + 2) ^ E)) ≤ law.mass retained ∧
        (∀ z ∈ retained, ∃ r, 0 < r ∧
          ∃ (slice : ResidueBoxSlice (fun _ : K => S) r)
            (hlen : ∀ j, 0 < slice.length j),
            (∀ j, Real.exp (-(p + extra)) * (S : ℝ) ≤ (slice.length j : ℝ)) ∧
            localLaw z = slice.fullSliceLaw hlen) ∧
        ∀ z ∈ retained, Real.exp (-((q + 2) ^ E)) ≤ (localLaw z).mean
          (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
            (B.shearTransformedSlots hw
              ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue Ψ) := by
  obtain ⟨E, hE, hfixed⟩ := exists_relative_finite_returned_slice_normalization s
  refine ⟨E, hE, ?_⟩
  intro n₀ K X _ _ _ _ P _ e S hS i p a Λ σ extra hp ha hΛ hσ hσ1 hextra
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  let τ := unconditionedSpatialTrimFraction (Fintype.card X) σ
  let W := trimmedSpatialWidths (K := K) ((Fintype.card K : ℝ) * S) τ N
  let R := spatialTrimMargin τ N
  let q := p + extra + (Fintype.card K : ℝ) + 2
  let D := min d₀ ⌊p + extra⌋₊
  have hBP : unconditionedResidueSiteBound P ≤ (Fintype.card K : ℝ) * S := by
    exact unconditionedResidueSiteBound_le_commonSide P e S hPS
  obtain ⟨hW, hR, hZ, productive, hmass, hinj, hreturn, _⟩ :=
    exists_unconditioned_rootBudget_absolute_family_equiv s n₀ P e
      ((Fintype.card K : ℝ) * S) hBP i ha hσ hσ1 d₀ habsolute
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
  have hτ : 0 ≤ τ :=
    (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hσ hσ1).1.le
  have hinside (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)
      (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
      jointIntegerPhysicalSite x (z.1.val,z.2.val) ∈ integerBox N := by
    exact unconditionedCommonSide_site_mem S hτ N hR z x hx
  have hbound (z : trimmedIntegerBox N R × rectangularWeightIndices 0 W 1)
      (x : K → ℤ) (hx : x ∈ integerBox (fun _ : K => S)) :
      f (jointIntegerPhysicalSite x (z.1.val,z.2.val)) ∈ Set.Icc (0 : ℝ) 1 :=
    hf _ (hinside z x hx)
  have hreturned (z) (hz : z ∈ productive) :
      RelativePatchSliceConclusion s (fun _ : K => S)
        (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) Λ d₀ (p + extra) := by
    have hprimeReturn : RelativePatchSliceConclusion s
        (coordinateReindexedSides e (fun k => P (e k)))
        (coordinateReindexedFunction e
          (fun x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val)))) Λ d₀ p := by
      have he : coordinateReindexedSides e (fun k => P (e k)) = P := by
        funext j
        exact congrArg P (e.apply_symm_apply j)
      rw [he]
      exact hreturn z hz
    apply (hprimeReturn.coordinateReturn e).enlargeBox (fun k => hPS (e k))
      (fun k => ?_) hextra
    calc
      Real.exp (-extra) * (S : ℝ) ≤
          Real.exp (-extra) * (Real.exp extra * (P (e k) : ℝ)) :=
        mul_le_mul_of_nonneg_left (hratio (e k)) (Real.exp_nonneg _)
      _ = (P (e k) : ℝ) := by rw [← mul_assoc, ← Real.exp_add]; simp
  obtain ⟨localLaw, d, w, hw, Ψ, B, localForm, retained, hd, hd₀, hpos, hws, hΨ, hB,
      hsub, hretained, hcertificate, hlocal⟩ :=
    hfixed law productive hprod (fun _ : K => S) (fun _ => hS) (p + extra)
      (add_nonneg hp hextra) Λ hΛ d₀
      (fun z x => f (jointIntegerPhysicalSite x (z.1.val,z.2.val))) hbound hreturned
  refine ⟨hW, hR, hZ, productive, hmass, hinj, hinside, d, w, hw, Ψ, B,
    localForm, localLaw, retained, hd₀, hd, hpos, hws, hΨ, hB, hsub,
    hretained, ?_, hcertificate, hlocal⟩
  have hle := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hmass
      (by positivity : (0 : ℝ) ≤ ((D + 1) * (s + 1) ^ D : ℕ)))
    (Real.exp_nonneg (-((q + 2) ^ E)))
  exact hle.trans hretained

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

private structure ScalarCommonBoxSource {K X : Type} [Fintype K] [Fintype X]
    [DecidableEq K] (s d₀ D : ℕ) (N : X → ℕ) (τ : ℝ) (sides : K → ℕ)
    (W : Option K × X → ℝ) (f : (X → ℤ) → ℝ) (Λ cost budget mass : ℝ) where
  width_pos : ∀ z, 0 < W z
  proper : ∀ x, 2 * spatialTrimMargin τ N x < N x
  smooth_pos : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z
  rank : ℕ
  patch : PolynomialPatch K s rank
  rank_le : rank ≤ d₀
  rank_le_early : rank ≤ D
  lip_le : (patch.kernel.lip : ℝ) ≤ Real.exp budget
  center_le : ∀ j, realPolynomialMass (patch.form.center j) ≤ budget
  localForm : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → PolynomialSlots K rank patch.weight
  localLaw : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → FiniteProbabilityWeights (integerBox sides)
  retained : Finset (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1)
  mass_le : mass ≤ (selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
    (trimmedIntegerBox_nonempty N _ proper) (fun _ : X => 1) {0} W width_pos smooth_pos).mass retained
  slice : ∀ z ∈ retained,
    RelativeReturnedFiberLaw (fun _ : K => True) sides cost (localLaw z)
  score : ∀ z ∈ retained, Real.exp (-budget) ≤ (localLaw z).mean
    (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
      (patch.form.shearTransformedSlots patch.weight_mono
        ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue patch.kernel)

variable {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "Vars" => LayerSamplerVariables G I n B

theorem exists_allocatedZeroLayer_commonSide_initialization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (n₀ : ℕ) (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ surplus extra : ℝ},
      0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      0 < surplus → surplus ≤ 1 → 0 ≤ extra →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp extra * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card Vars : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) surplus)
        (unconditionedCollisionWidth P surplus) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + surplus ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) surplus
      let q := p + extra + (Fintype.card Vars : ℝ) + 2
      let D := min d₀ ⌊p + extra⌋₊
      let mass := ((surplus / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
        Real.exp (-((q + 2) ^ C))
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch Vars s d),
        d ≤ d₀ ∧ d ≤ D ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp ((q + 2) ^ C) ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ (q + 2) ^ C) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          (p + extra) mass (Real.exp (-((q + 2) ^ C))),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨C, hC, hsource⟩ := exists_unconditioned_commonSide_fixed_patch_family s
  refine ⟨C, hC, ?_⟩
  intro S n₀ eG P _ i p a Λ surplus extra hp ha hΛ hsurplus hsurplus1 hextra
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
    τ q D mass
  let e := (zeroLayerVariablesEquiv B).trans eG
  have hfamily := hsource n₀ P e S.value S.positive i hp ha hΛ hsurplus hsurplus1
    hextra hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  obtain ⟨hW, hproper, hZ, productive, _hmass, _hinjective, _hinside,
    d, w, hw, Ψ, form, localForm, localLaw, retained, hd₀, hdD, hpos, hws,
    hΨ, hform, _hsub, _hmassRelative, hretained, hslice, hscore⟩ := hfamily
  let patch : PolynomialPatch Vars s d := ⟨w, hpos, hws, hw, form, Ψ⟩
  have hslice0 : ∀ z ∈ retained, RelativeReturnedFiberLaw (fun _ : Vars => True)
      (fun _ : Vars => S.value) (p + extra) (localLaw z) := by
    intro z hz
    obtain ⟨r, hr, slice, hlen, hdense, hlawSlice⟩ := hslice z hz
    rw [hlawSlice]
    exact slice.fullSliceLaw_returnedFiberLaw hr hlen hdense
  let data : ScalarCommonBoxSource s d₀ D N τ (fun _ : Vars => S.value)
      (trimmedSpatialWidths (K := Vars) ((Fintype.card Vars : ℝ) * S.value) τ N)
      f Λ (p + extra) ((q + 2) ^ C) mass :=
    ⟨hW, hproper, hZ, d, patch, hd₀, hdD, hΨ, hform, localForm, localLaw,
      retained, hretained, hslice0, hscore⟩
  have hwidth : allocatedExternalCandidateWidths B U b S N τ 1 =
      trimmedSpatialWidths (K := Vars) ((Fintype.card Vars : ℝ) * S.value) τ N := by
    rw [allocatedExternalCandidateWidths_zero_layers, zeroLayerVariables_card]
  have actualData : ScalarCommonBoxSource s d₀ D N τ
      (allocatedExternalCandidateSides B U b S)
      (allocatedExternalCandidateWidths B U b S N τ 1)
      f Λ (p + extra) ((q + 2) ^ C) mass := by
    rw [allocatedExternalCandidateSides_zero_layers_fun, hwidth]
    exact data
  have hNpos (x : X) : 0 < N x := by have hx := actualData.proper x; omega
  have hτ : 0 < τ :=
    (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hsurplus hsurplus1).1
  let A := allocatedExternalCandidateSampler_zero_layers B U b S hb o hR hσ poly hm
    0 N τ 1 (fun _ => 1) {0} hNpos hτ (by norm_num) (fun _ => by norm_num)
    (trimmedIntegerBox_nonempty N _ actualData.proper) actualData.smooth_pos
  let := polynomialShearIndexFintype actualData.patch.weight actualData.patch.weight_pos
  have hlaw : A.law = selectedJointReference
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (trimmedIntegerBox_nonempty N _ actualData.proper) (fun _ : X => 1) {0}
      (allocatedExternalCandidateWidths B U b S N τ 1)
      actualData.width_pos actualData.smooth_pos :=
    A.law_zero_layers
  have hmassA : mass ≤ A.law.mass actualData.retained := by
    rw [hlaw]
    exact actualData.mass_le
  have hsliceA := actualData.slice
  have hdec : (fun _ : Vars => instDecidableTrue) =
      (fun _ : Vars => Classical.propDecidable True) := Subsingleton.elim _ _
  rw [hdec] at hsliceA
  obtain ⟨Q, _, _, hcenter, hkeep⟩ :=
    exists_allocatedZeroLayerNormalizedShearProblem (E := E) A (fun _ => True) actualData.retained
      hmassA (fun j => (j.property trivial).elim) actualData.patch actualData.localForm
      actualData.localLaw hsliceA f Λ actualData.score
  exact ⟨A, actualData.rank, actualData.patch, actualData.rank_le,
    actualData.rank_le_early, actualData.lip_le, actualData.center_le, Q, hcenter, hkeep⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

private structure UniformScalarCommonBoxSource {K X : Type} [Fintype K] [Fintype X]
    [DecidableEq K] (s d₀ D : ℕ) (N : X → ℕ) (τ : ℝ) (sides : K → ℕ)
    (W : Option K × X → ℝ) (f : (X → ℤ) → ℝ) (Λ cost budget mass : ℝ) where
  width_pos : ∀ z, 0 < W z
  proper : ∀ x, 2 * spatialTrimMargin τ N x < N x
  smooth_pos : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0} W z
  rank : ℕ
  patch : PolynomialPatch K s rank
  rank_le : rank ≤ d₀
  rank_le_early : rank ≤ D
  lip_le : (patch.kernel.lip : ℝ) ≤ Real.exp budget
  center_le : ∀ j, realPolynomialMass (patch.form.center j) ≤ budget
  localForm : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → PolynomialSlots K rank patch.weight
  localLaw : (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1) → FiniteProbabilityWeights (integerBox sides)
  retained : Finset (trimmedIntegerBox N (spatialTrimMargin τ N) ×
    rectangularWeightIndices 0 W 1)
  mass_le : mass ≤ (selectedJointReference (trimmedIntegerBox N (spatialTrimMargin τ N))
    (trimmedIntegerBox_nonempty N _ proper) (fun _ : X => 1) {0} W width_pos smooth_pos).mass retained
  slice : ∀ z ∈ retained,
    RelativeReturnedFiberLaw (fun _ : K => True) sides cost (localLaw z)
  score : ∀ z ∈ retained, Real.exp (-budget) ≤ (localLaw z).mean
    (fun x => (f (jointIntegerPhysicalSite x.val (z.1.val,z.2.val)) - Λ) *
      (patch.form.shearTransformedSlots patch.weight_mono
        ((localForm z).loweringAt (fun j => (x.val j : ℝ)))).patchValue patch.kernel)

theorem exists_allocatedZeroLayer_commonSide_initialization_uniform (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∀ (S : LayerSamplerScale (G := G) B U b R σ)
      (n₀ : ℕ) (_eG : G ≃ Fin n₀)
      (P : Fin n₀ → ℕ) [∀ j, NeZero (P j)] (_i : X)
      {p a Λ surplus extra : ℝ},
      0 ≤ p → 0 ≤ a → Λ ∈ Set.Icc (0 : ℝ) 1 →
      0 < surplus → surplus ≤ 1 → 0 ≤ extra →
      (∀ j, P j ≤ S.value) →
      (∀ j, (S.value : ℝ) ≤ Real.exp extra * (P j : ℝ)) →
      ∀ (d₀ : ℕ), RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
      (∀ j, (P j).Prime) → Function.Injective P →
      (∀ j k, P j ≤ 2 ^ (n₀ + 1) * P k) →
      (∀ j, Real.exp p ≤ (P j : ℝ)) →
      ∀ (N : X → ℕ),
      (∀ x, unconditionedSpatialWidthCutoff
        ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value)
        (unconditionedSpatialTrimFraction (Fintype.card X) surplus)
        (unconditionedCollisionWidth P surplus) ≤ (N x : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
      a + surplus ≤ (𝔼 x ∈ integerBox N, f x) →
      let τ := unconditionedSpatialTrimFraction (Fintype.card X) surplus
      let q := p + extra + (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
      let D := min d₀ ⌊p + extra⌋₊
      let mass := ((surplus / 4) / ((D + 1) * (s + 1) ^ D : ℕ)) *
        Real.exp (-((q + 2) ^ C))
      ∃ (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
          N poly hm τ 1 (fun _ => 1) {0} 0)
        (d : ℕ) (patch : PolynomialPatch (LayerSamplerVariables G I n B) s d),
        d ≤ d₀ ∧ d ≤ D ∧
        (patch.kernel.lip : ℝ) ≤ Real.exp ((q + 2) ^ C) ∧
        (∀ j, realPolynomialMass (patch.form.center j) ≤ (q + 2) ^ C) ∧
        letI := polynomialShearIndexFintype patch.weight patch.weight_pos
        ∃ Q : AllocatedExternalCandidateProblem (E := E) A
          (polynomialShearNilmanifold patch.weight s patch.weight_le)
          (RationalTorus.trivialFiltration s) 0 1
          (fun _ y => (patch.shearObservable y : ℂ))
          (fun x => ((f x - Λ : ℝ) : ℂ))
          (p + extra) mass (Real.exp (-((q + 2) ^ C))),
          Q.centerLift = allocatedZeroLayerCenterLift U ∧
          ∀ z, (Q.chart z).keep = fun _ => True := by
  obtain ⟨C, hC, hsource⟩ := exists_unconditioned_commonSide_fixed_patch_family s
  refine ⟨C, hC, ?_⟩
  intro G X _ _ I E J _ _ n B _ U b R σ hb o hR hσ poly hm _
    S n₀ eG P _ i p a Λ surplus extra hp ha hΛ hsurplus hsurplus1 hextra
    hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
    τ q D mass
  let e := (zeroLayerVariablesEquiv B).trans eG
  have hfamily := hsource n₀ P e S.value S.positive i hp ha hΛ hsurplus hsurplus1
    hextra hPS hratio d₀ habsolute hprime hdistinct hcomparable hcutoff N hN f hf hfree hmean
  obtain ⟨hW, hproper, hZ, productive, _hmass, _hinjective, _hinside,
    d, w, hw, Ψ, form, localForm, localLaw, retained, hd₀, hdD, hpos, hws,
    hΨ, hform, _hsub, _hmassRelative, hretained, hslice, hscore⟩ := hfamily
  let patch : PolynomialPatch (LayerSamplerVariables G I n B) s d := ⟨w, hpos, hws, hw, form, Ψ⟩
  have hslice0 : ∀ z ∈ retained, RelativeReturnedFiberLaw (fun _ : (LayerSamplerVariables G I n B) => True)
      (fun _ : (LayerSamplerVariables G I n B) => S.value) (p + extra) (localLaw z) := by
    intro z hz
    obtain ⟨r, hr, slice, hlen, hdense, hlawSlice⟩ := hslice z hz
    rw [hlawSlice]
    exact slice.fullSliceLaw_returnedFiberLaw hr hlen hdense
  let data : UniformScalarCommonBoxSource s d₀ D N τ (fun _ : (LayerSamplerVariables G I n B) => S.value)
      (trimmedSpatialWidths (K := (LayerSamplerVariables G I n B)) ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value) τ N)
      f Λ (p + extra) ((q + 2) ^ C) mass :=
    ⟨hW, hproper, hZ, d, patch, hd₀, hdD, hΨ, hform, localForm, localLaw,
      retained, hretained, hslice0, hscore⟩
  have hwidth : allocatedExternalCandidateWidths B U b S N τ 1 =
      trimmedSpatialWidths (K := (LayerSamplerVariables G I n B)) ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value) τ N := by
    rw [allocatedExternalCandidateWidths_zero_layers, zeroLayerVariables_card]
  have actualData : UniformScalarCommonBoxSource s d₀ D N τ
      (allocatedExternalCandidateSides B U b S)
      (allocatedExternalCandidateWidths B U b S N τ 1)
      f Λ (p + extra) ((q + 2) ^ C) mass := by
    rw [allocatedExternalCandidateSides_zero_layers_fun, hwidth]
    exact data
  have hNpos (x : X) : 0 < N x := by have hx := actualData.proper x; omega
  have hτ : 0 < τ :=
    (unconditionedSpatialTrimFraction_bounds (Fintype.card X) hsurplus hsurplus1).1
  let A := allocatedExternalCandidateSampler_zero_layers B U b S hb o hR hσ poly hm
    0 N τ 1 (fun _ => 1) {0} hNpos hτ (by norm_num) (fun _ => by norm_num)
    (trimmedIntegerBox_nonempty N _ actualData.proper) actualData.smooth_pos
  let := polynomialShearIndexFintype actualData.patch.weight actualData.patch.weight_pos
  have hlaw : A.law = selectedJointReference
      (trimmedIntegerBox N (spatialTrimMargin τ N))
      (trimmedIntegerBox_nonempty N _ actualData.proper) (fun _ : X => 1) {0}
      (allocatedExternalCandidateWidths B U b S N τ 1)
      actualData.width_pos actualData.smooth_pos :=
    A.law_zero_layers
  have hmassA : mass ≤ A.law.mass actualData.retained := by
    rw [hlaw]
    exact actualData.mass_le
  have hsliceA := actualData.slice
  have hdec : (fun _ : (LayerSamplerVariables G I n B) => instDecidableTrue) =
      (fun _ : (LayerSamplerVariables G I n B) => Classical.propDecidable True) := Subsingleton.elim _ _
  rw [hdec] at hsliceA
  obtain ⟨Q, _, _, hcenter, hkeep⟩ :=
    exists_allocatedZeroLayerNormalizedShearProblem (E := E) A (fun _ => True) actualData.retained
      hmassA (fun j => (j.property trivial).elim) actualData.patch actualData.localForm
      actualData.localLaw hsliceA f Λ actualData.score
  exact ⟨A, actualData.rank, actualData.patch, actualData.rank_le,
    actualData.rank_le_early, actualData.lip_le, actualData.center_le, Q, hcenter, hkeep⟩

end Erdos3.VectorPolynomial

end

end OAI
