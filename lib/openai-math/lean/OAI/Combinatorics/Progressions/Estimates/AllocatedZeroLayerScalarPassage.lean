import OAI.Combinatorics.Progressions.Estimates.ComparableScalarPhysicalFamilyPatch
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllKeptSliceLaw
import OAI.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllSiteLaw
import OAI.Combinatorics.Progressions.Sampling.AllocatedZeroLayerPhysicalPatchScore

namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w x
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def IndexedComparableScalarSharedSliceTailStatement (s d r : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type x} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level density : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    0 < density → density⁻¹ ≤ Real.exp p →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : K → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ r * L) →
    ∀ {κ : Type w} [Fintype κ] [Nonempty κ]
      (stride : κ → ℕ) (S : ∀ c, ResidueBoxSlice parameters (stride c)),
      (∀ c, 0 < stride c) → (∀ c, stride c ≤ ⌈2 / density⌉₊) →
      (∀ c j, density * L / 2 ≤ ((S c).length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ c j, (0 : ℤ) < (S c).length j),
    budget ≤ (p + F) ^ F ∧
    ∀ (c : κ) (h : (I → ℤ) → ℂ),
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : K => (0 : ℤ)) (fun j => ((S c).length j : ℤ)) (hparam c)).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => ((S c).start j : ℤ) + (stride c : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => ((S c).start j : ℤ) + (stride c : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_indexed_comparable_scalar_shared_slice_tail (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    IndexedComparableScalarSharedSliceTailStatement.{u,v,w,x} s d r epsilon := by
  obtain ⟨A, C, F, hA, hC, hF, htransfer⟩ :=
    exists_indexed_comparable_unconditioned_scalar_slice_transfer.{u,v,x} s d r hd hr hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro K _ _ hK I V _ _ _ _ _ _ _ d0 nilmanifold p σ level density hp hn hσ hσ1 hσinv
    hlevel hlevel2 hdensity hdensityInv g hg target budget L parameters hlo hhi
    κ _ _ stride S hq hqCap hlength N hN hunit τ Wsite width margin
  have hfamily (c : κ) := htransfer hK nilmanifold hp hn hσ hσ1 hσinv hlevel hlevel2
    hdensity hdensityInv g hg parameters hlo hhi (stride c) (S c) (hq c) (hqCap c)
    (hlength c) N hN hunit
  choose hwidth hmargin hZ hparam hbudget htail using hfamily
  let c0 : κ := Classical.choice inferInstance
  refine ⟨hwidth c0, hmargin c0, hZ c0, hparam, hbudget c0, ?_⟩
  intro c h hh hnoincrement
  exact htail c h hh hnoincrement

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

theorem exists_indexed_comparable_scalar_retained_slice_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ C F : ℕ, 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d),
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {p σ Λ density accuracy gain : ℝ},
    2 ≤ p → (Fintype.card I : ℝ) ≤ p →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-p) ≤ (1 - τ) * Λ →
    0 < density → density ≤ 1 → density⁻¹ ≤ Real.exp p →
    0 < accuracy → accuracy ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE p → relativePatchComplexity P ≤ p →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    let Q := ⌈2 / density⌉₊
    let meshCap := denseResidueMeshCap d density accuracy (r : ℝ)
    Real.exp (-target) < gain - accuracy / 2 →
    16 * ((d : ℝ) + 1) / (accuracy * density) ≤ L →
    ∀ parameters : K → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      (Fintype.card (DenseResidueSliceNetCode K Q meshCap) : ℝ) * Real.exp (-target) <
        outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        gain ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨heps, heps1⟩ := relativeScalarPassageSlack_bounds hτ hτhalf
  obtain ⟨_, C, F, _, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_shared_slice_tail.{u,v,w,w} s d r hd hr heps heps1
  refine ⟨C, F, hC, hF, ?_⟩
  intro K _ decK hK I V _ _ _ _ _ _ _ d₀ rank nilmanifold p σ Λ density accuracy gain hp hn
    hσ hσ1 hσinv hΛ hlevel hdensity hdensity1 hdensityInv haccuracy haccuracy1
    P g hg hP hgval target budget L Q meshCap hgap hmesh parameters hlo hhi N hN f hf
    trim Wsite width margin
  let : Nonempty K := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card K)
  have hnetExists :=
    exists_denseResidueScalarScore_net K hdensity hdensity1 haccuracy haccuracy1
      (show (1 : ℝ) ≤ r by exact_mod_cast (show 1 ≤ r by omega))
      L (by simpa only [hK] using hmesh) parameters (fun j => ⟨hlo j, hhi j⟩)
  rw [hK] at hnetExists
  obtain ⟨stride, slices, hlen, hstride, hlength, hnet⟩ := hnetExists
  have hlevel2 : (1 - τ) * Λ ≤ 2 := by nlinarith [hΛ.1, hΛ.2]
  have hunit (x : I → ℤ) (_hx : x ∈ translatedIntegerBox (0 : I → ℤ) N) :
      (g.eval x).im = 0 ∧ 0 ≤ (g.eval x).re ∧ (g.eval x).re ≤ 1 := by
    rw [hgval]
    exact ⟨Complex.ofReal_im _, by simpa only [Complex.ofReal_re, Set.mem_Icc] using P.value_mem_Icc _⟩
  obtain ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩ :=
    hscalar hK nilmanifold hp hn hσ hσ1 hσinv hlevel hlevel2 hdensity hdensityInv g hg
      parameters hlo hhi stride slices (fun c => (hstride c).1) (fun c => (hstride c).2)
      hlength N hN hunit
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained hmass hinside hretained
  let h : (I → ℤ) → ℂ := fun x => ((f x * P.value (fun i => (x i : ℝ)) : ℝ) : ℂ)
  have hgf : g.eval = fun x => (P.value (fun i => (x i : ℝ)) : ℂ) := funext hgval
  have hh (x : I → ℤ) (hx : x ∈ translatedIntegerBox (0 : I → ℤ) N) :
      0 ≤ (h x).re ∧ (h x).re ≤ 1 := by
    change 0 ≤ f x * P.value _ ∧ f x * P.value _ ≤ 1
    refine ⟨mul_nonneg (hf x hx).1 (P.value_mem_Icc _).1, ?_⟩
    calc
      f x * P.value _ ≤ 1 * P.value _ :=
        mul_le_mul_of_nonneg_right (hf x hx).2 (P.value_mem_Icc _).1
      _ ≤ 1 := by simpa only [one_mul] using (P.value_mem_Icc _).2
  obtain ⟨c, lo, H, M, a, hM, hbox, hcost, hne, _, hscore⟩ :=
    exists_residue_slice_of_rectangular_scalar_family outer
      (fun z i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) 0 N
      (fun _ => h) (fun _ => g.eval) (fun _ => relativeScalarPassageSlack τ)
      (fun _ => (1 - τ) * Λ) (fun _ => budget) stride
      (fun c j => ((slices c).start j : ℤ)) (fun _ => 0)
      (fun c j => ((slices c).length j : ℤ)) hparam target
      (fun c hupper => by
        have hdec : decK =
            (fun a b => Classical.propDecidable (a = b)) := Subsingleton.elim _ _
        have ht := htail c h hh hupper
        rw [hdec] at ht
        simpa only [rectangularScalarDiscrepancy, outer, margin, width, Wsite, trim, target, Pi.zero_def]
          using ht)
      retained (by simpa only [hK] using hmass) (by
        intro z hz
        obtain ⟨q, hq, S, hS, hdense, hscore⟩ := hretained z hz
        obtain ⟨c, hc⟩ := hnet P f 0 N
          (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)
          (hinside z hz) hf hτ hτhalf hΛ q hq S hS hdense hscore
        refine ⟨c, hgap.trans_le ?_⟩
        simpa only [h, hgf] using hc)
  have hpTarget : p ≤ target := by
    dsimp [target]
    nlinarith [Nat.cast_nonneg (α := ℝ) (r * d)]
  have htargetBudget : target ≤ budget := by
    have hbase : 1 ≤ target + 2 := by linarith
    have hpow := le_self_pow₀ hbase (by omega : C ≠ 0)
    change target ≤ (target + 2) ^ C
    linarith
  have hresult := relativePatchSliceConclusion_of_scalarNiltest nilmanifold N f P g h hgval
    (fun x => by simp only [h, hgval, Complex.ofReal_mul])
    lo H M a ((1 - τ) * Λ) budget hM hbox hne hcost
    (hP.trans (hpTarget.trans htargetBudget)) hscore
  exact hresult.mono le_rfl hbudgetFinal

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card
  trimmedSpatialWidths spatialTrimMargin rectangularWeightIndices unconditionedSpatialTrimFraction
  selectedResidueSmoothWeight RelativePatchSliceConclusion
  FiniteProbabilityWeights.eventProbability

theorem exists_indexed_comparable_scalar_early_retained_slice_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ E C F : ℕ, 2 ≤ E ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d)
      {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {b σ Λ density : ℝ},
    2 ≤ b → (Fintype.card I : ℝ) ≤ b →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp b →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ Λ →
    Real.exp (-b) ≤ density → density ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE b → relativePatchComplexity P ≤ b →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let p := (b + 2) ^ E
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ parameters : K → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      Real.exp (-b) ≤ outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        Real.exp (-b) ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨E, hE, hnumeric⟩ := exists_relativeScalarNetPassage_power_budget d r (by omega)
  obtain ⟨C, F, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_retained_slice_patch.{u,v,w} s d r hd hr hτ hτhalf
  refine ⟨E, C, F, hE, hC, hF, ?_⟩
  intro K _ decK hK I V _ _ _ _ _ _ _ d₀ rank nilmanifold b σ Λ density hb hn
    hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
    p target budget L parameters hlo hhi N hN f hf trim Wsite width margin
  obtain ⟨hp, hbp, _hcard, hmass, hgap, hlevel, hdensityInv, _hQ,
      _hhalf, _hratio, _hwidth, hmesh, _hlong⟩ := hnumeric b density hb hdensity hdensity1
  have hbp' : b ≤ p := by linarith
  have hn' : (Fintype.card I : ℝ) ≤ p := hn.trans hbp'
  have hσinv' : σ⁻¹ ≤ Real.exp p := hσinv.trans (Real.exp_le_exp.mpr hbp')
  have hdensity0 : 0 < density := (Real.exp_pos (-b)).trans_le hdensity
  have haccuracy1 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpTarget : p ≤ target := by
    dsimp only [target]
    nlinarith [Nat.cast_nonneg (α := ℝ) (r*d)]
  have htargetBudget : target ≤ budget := by
    have hbase : 1 ≤ target + 2 := by linarith
    have hh := le_self_pow₀ hbase (by omega : C ≠ 0)
    change target ≤ (target + 2)^C
    linarith
  obtain ⟨hwidth, hmargin, hZ, hpassage⟩ :=
    hscalar hK nilmanifold hp hn' hσ hσ1 hσinv' hΛ (hlevel Λ τ hΛlower hτhalf)
      hdensity0 hdensity1 hdensityInv (Real.exp_pos (-b)) haccuracy1
      P g (hg.mono hbp') (hP.trans hbp') hgeval hgap
      (hmesh budget (hpTarget.trans htargetBudget)) parameters hlo hhi N hN f hf
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained hretained hinside hscore
  apply hpassage retained
  · simpa only [DenseResidueSliceNetCode.card, hK, Fintype.card_fin,
      outer, margin, width, Wsite, trim] using hmass.trans_le hretained
  · exact hinside
  · exact hscore

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card trimmedSpatialWidths spatialTrimMargin
  rectangularWeightIndices unconditionedSpatialTrimFraction selectedResidueSmoothWeight
  RelativePatchSliceConclusion FiniteProbabilityWeights.eventProbability

theorem exists_indexed_comparable_scalar_physical_family_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ E C F : ℕ, 2 ≤ E ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d)
      {I : Type u} {V : Type v} [Fintype I] [_decI : DecidableEq I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {b σ Λ density : ℝ},
    2 ≤ b → (Fintype.card I : ℝ) ≤ b →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp b →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ Λ →
    Real.exp (-b) ≤ density → density ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE b → relativePatchComplexity P ≤ b →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let p := (b + 2) ^ E
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : K → ℕ) [∀ j, NeZero (parameters j)],
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := unconditionedResidueSiteBound parameters
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ (retained : Finset (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1))
      (localLaw : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) →
        FiniteProbabilityWeights (integerBox parameters)),
      Real.exp (-b) ≤ outer.mass retained →
      (∀ z ∈ retained, ∀ u : integerBox parameters,
        jointIntegerPhysicalSite u.val (z.1.val,z.2.val) ∈
          integerBox N) →
      (∀ z ∈ retained, ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        localLaw z = S.fullSliceLaw hlen) →
      (∀ z ∈ retained, Real.exp (-b) ≤ (localLaw z).mean (fun u =>
        (f (jointIntegerPhysicalSite u.val (z.1.val,z.2.val)) - Λ) *
          P.value (fun i => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨E, C, F, hE, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_early_retained_slice_patch.{u,v,w} s d r hd hr hτ hτhalf
  refine ⟨E, C, F, hE, hC, hF, ?_⟩
  intro K _ decK hK I V _ decI _ _ _ _ _ _ d₀ rank nilmanifold b σ Λ density hb hn
    hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
    p target budget L parameters _ hlo hhi N hN f hf trim Wsite width margin
  have hdec : decI = Classical.decEq I := Subsingleton.elim _ _
  subst decI
  have hzero : translatedIntegerBox (0 : I → ℤ) N = integerBox N := by
    ext x
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hf' : ∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [hzero] using hf
  obtain ⟨hwidth, hmargin, hZ, hpassage⟩ :=
    hscalar hK nilmanifold hb hn hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
      parameters hlo hhi N hN f hf'
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained localLaw hmass hinside hslice hscore
  apply hpassage (fun z => z ∈ retained)
  · change Real.exp (-b) ≤ outer.eventProbability (fun z => z ∈ retained)
    rw [FiniteProbabilityWeights.eventProbability_mem]
    exact hmass
  · intro z hz u
    rw [hzero]
    simpa only [smoothAffineSample_jointIntegerFrame] using hinside z hz u
  · intro z hz
    obtain ⟨q, hq, S, hlen, hdense, hlaw⟩ := hslice z hz
    refine ⟨q, hq, S, hlen, hdense, ?_⟩
    have h := hscore z hz
    rw [hlaw] at h
    simpa only [smoothAffineSample_jointIntegerFrame] using h

end
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] selectedJointReference trimmedIntegerBox
  trimmedSpatialWidths spatialTrimMargin rectangularWeightIndices
  unconditionedSpatialTrimFraction selectedResidueSmoothWeight
  AllocatedExternalCandidateProblem.Conclusion.allSiteLaw

theorem exists_allocatedZeroLayer_scalar_passage (s n₀ ratio : ℕ)
    (hn₀ : 2 ≤ n₀) (hratio : 2 ≤ ratio)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ scalarE scalarC scalarF : ℕ,
      2 ≤ scalarE ∧ 2 ≤ scalarC ∧ 2 ≤ scalarF ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
      {I Ecol J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
      {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {σsurplus : ℝ}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm
        (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
        (fun _ : X => 1) {0} center)
      (_hK : Fintype.card (LayerSamplerVariables G I n B) = n₀)
      {V : Type} {d : ℕ} (patch : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex patch.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      {f : (X → ℤ) → ℝ} {lam cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := Ecol) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold)
      (_hkeep : ∀ z : P.productive, (P.chart z).keep = (fun _ => True))
      {outputCost outputMass outputScore : ℝ}
      (out : P.Conclusion outputCost outputMass outputScore)
      (b : ℝ), 2 ≤ b → (Fintype.card X : ℝ) ≤ b →
      0 < σsurplus → σsurplus ≤ 1 → σsurplus⁻¹ ≤ Real.exp b →
      lam ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ lam →
      0 ≤ outputCost → outputCost ≤ b →
      Real.exp (-b) ≤ outputMass → Real.exp (-b) ≤ outputScore →
      relativePatchComplexity patch ≤ b →
      ∀ g : (polynomialShearNilmanifold patch.weight s patch.weight_le).Niltest
        (fun _ : X => 1), g.ComplexityLE b →
      (∀ x : X → ℤ, g.eval x =
        ((patch.ofZeroLayerShearOrbit out.ambient).value (fun i => (x i : ℝ)) : ℂ)) →
      let p := (b + 2) ^ scalarE
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (p + 1)
      let budget := (target + 2) ^ scalarC
      (∀ i, Real.exp budget ≤ (A.sides i : ℝ)) →
      (∀ i, (A.sides i : ℝ) ≤ (ratio : ℝ) * Real.exp budget) →
      (∀ i, Real.exp ((p + scalarF) ^ scalarF) ≤ (N i : ℝ)) →
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      RelativePatchSliceConclusion s N f ((1 - discount) * lam) d
        ((p + scalarF) ^ scalarF) := by
  obtain ⟨scalarE, scalarC, scalarF, hE, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_physical_family_patch s n₀ ratio
      hn₀ hratio hdiscount hdiscountHalf
  refine ⟨scalarE, scalarC, scalarF, hE, hC, hF, ?_⟩
  intro G X _ _ I Ecol J _ _ n B _ U basis R σ S hb o hR hσ N poly hm
    σsurplus center _ A hK V d patch _ _ _ _ _ f lam cost massThreshold scoreThreshold
    P hkeep outputCost outputMass outputScore out b hb2 hX hsurplus hsurplus1 hsurplusInv
    hlam hlamLower houtputCost houtputCostB hmass hscore hpatch g hg heval
    p target budget hlo hhi hN hf
  let : ∀ i, NeZero (A.sides i) := fun i => ⟨(A.sides_pos i).ne'⟩
  have hdensity : Real.exp (-b) ≤ Real.exp (-outputCost) :=
    Real.exp_le_exp.mpr (neg_le_neg houtputCostB)
  have hdensity1 : Real.exp (-outputCost) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr houtputCost)
  have hphysicalPatch : relativePatchComplexity (patch.ofZeroLayerShearOrbit out.ambient) ≤ b :=
    hpatch
  have hresult := hscalar hK (polynomialShearNilmanifold patch.weight s patch.weight_le)
    hb2 hX hsurplus hsurplus1 hsurplusInv hlam hlamLower hdensity hdensity1
    (patch.ofZeroLayerShearOrbit out.ambient) g hg hphysicalPatch heval
    A.sides hlo hhi N hN f hf
  have hwidth := allocatedExternalCandidateWidths_eq_scalar_zero_layers
    B U basis S N (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
  dsimp only at hresult
  rw [← hwidth] at hresult
  obtain ⟨hwidth', hmargin, hZ, hpassage⟩ := hresult
  have hlaw := AllocatedExternalCandidateSampler.law_zero_layers
    B U basis S hb o hR hσ poly hm center N
    (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
    (fun _ => 1) {0} A
  apply hpassage out.retained out.allSiteLaw
  · rw [← hlaw]
    exact hmass.trans out.mass
  · intro z _ u
    exact A.physical_mem_integerBox le_rfl z u
  · intro z hz
    obtain ⟨slice, hlen, hlength, heq⟩ := out.exists_fullSliceLaw hkeep ⟨z, hz⟩
    exact ⟨out.step ⟨z, hz⟩, out.step_pos ⟨z, hz⟩, slice, hlen, hlength,
      (out.allSiteLaw_of_mem z hz).trans heq⟩
  · intro z hz
    rw [out.allSiteLaw_of_mem z hz]
    exact hscore.trans (out.zeroLayer_siteLaw_score patch P ⟨z, hz⟩)

end Erdos3.VectorPolynomial

end

end OAI
