import OAI.Combinatorics.Progressions.Estimates.CanonicalUnconditionedScalarTransfer
import OAI.Combinatorics.Progressions.Probability.CanonicalScalarFamilyMass

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def rectangularScalarDiscrepancy {I J : Type*}
    [Fintype I] [Fintype J] (parent : I → ℤ) (H : I → ℕ)
    (h g : (I → ℤ) → ℂ) (epsilon level : ℝ) (D : ℕ)
    (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j)
    (z : Option J × I → ℤ) : ℝ :=
  (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
    realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (h x).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z) -
    (1 + epsilon) * level *
      realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (g x).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))

theorem exists_residue_slice_of_rectangular_scalar_family
    {C Ω I J : Type*} [Fintype C] [Fintype Ω] [Fintype I] [Fintype J]
    (outer : FiniteProbabilityWeights Ω) (source : Ω → Option J × I → ℤ)
    (parent : I → ℤ) (H : I → ℕ)
    (h g : C → (I → ℤ) → ℂ) (epsilon level budget : C → ℝ)
    (D : C → ℕ) (anchor parLo parHi : C → J → ℤ)
    (hpar : ∀ c j, parLo c j < parHi c j) (p : ℝ)
    (htransfer : ∀ c,
      ResidueSliceUpperComparison (h c) (g c) parent H (budget c) (level c)
          (Real.exp (-budget c)) →
      outer.eventProbability (fun z => Real.exp (-p) <
        rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
          (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) ≤ Real.exp (-p))
    (productive : Ω → Prop)
    (hmass : (Fintype.card C : ℝ) * Real.exp (-p) < outer.eventProbability productive)
    (hproductive : ∀ z, productive z → ∃ c, Real.exp (-p) <
      rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
        (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) :
    ∃ (c : C) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u : I → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧
      ResidueSliceLogCostLE H lo N M u (budget c) ∧
      Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u) ∧
      (∀ i, 0 < residueIndexLength (lo i) (lo i + N i) M (u i)) ∧
      Real.exp (-budget c) < (physicalResidueMean (h c) lo N M u).re -
        level c * (physicalResidueMean (g c) lo N M u).re := by
  have hfailure : ∃ c, ¬ ResidueSliceUpperComparison (h c) (g c) parent H
      (budget c) (level c) (Real.exp (-budget c)) := by
    by_contra! hn
    have hu := outer.eventProbability_union_bound productive
      (fun c z => Real.exp (-p) <
        rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
          (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) hproductive
    have hb : outer.eventProbability productive ≤ (Fintype.card C : ℝ) * Real.exp (-p) := by
      apply hu.trans
      calc
        _ ≤ ∑ _c : C, Real.exp (-p) := Finset.sum_le_sum (fun c _ => htransfer c (hn c))
        _ = _ := by simp
    exact (not_lt_of_ge hb) hmass
  obtain ⟨c, hc⟩ := hfailure
  obtain ⟨lo, N, M, u, hM, hbox, hcost, hne, hlength, hscore⟩ :=
    exists_nonempty_residue_slice_of_not_upper (Real.exp_nonneg _) hc
  exact ⟨c, lo, N, M, u, hM, hbox, hcost, hne, hlength, hscore⟩

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_residue_slice_of_canonical_scalar_family
    {C Ω I J : Type*} [Fintype C] [Fintype Ω] [Fintype I] [Fintype J]
    (outer : FiniteProbabilityWeights Ω) (source : Ω → Option J × I → ℤ)
    (parent : I → ℤ) (H : I → ℕ)
    (h g : C → (I → ℤ) → ℂ) (epsilon level budget : C → ℝ)
    (D : C → ℕ) (anchor parLo parHi : C → J → ℤ)
    (hpar : ∀ c j, parLo c j < parHi c j) (d : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hcard : (Fintype.card C : ℝ) ≤ Real.exp p)
    (htransfer : ∀ c,
      ResidueSliceUpperComparison (h c) (g c) parent H (budget c) (level c)
          (Real.exp (-budget c)) →
      outer.eventProbability (fun z => Real.exp (-(8 * ((d : ℝ) + 1) * (p + 1))) <
        rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
          (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) ≤ Real.exp (-(8 * ((d : ℝ) + 1) * (p + 1))))
    (productive : Ω → Prop)
    (hmass : Real.exp (-p) ≤ outer.eventProbability productive)
    (hproductive : ∀ z, productive z → ∃ c, Real.exp (-(8 * ((d : ℝ) + 1) * (p + 1))) <
      rectangularScalarDiscrepancy parent H (h c) (g c) (epsilon c) (level c)
        (D c) (anchor c) (parLo c) (parHi c) (hpar c) (source z)) :
    ∃ (c : C) (lo : I → ℤ) (N : I → ℕ) (M : ℕ) (u : I → ℤ),
      0 < M ∧ PhysicalSubbox parent H lo N ∧
      ResidueSliceLogCostLE H lo N M u (budget c) ∧
      Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u) ∧
      (∀ i, 0 < residueIndexLength (lo i) (lo i + N i) M (u i)) ∧
      Real.exp (-budget c) < (physicalResidueMean (h c) lo N M u).re -
        level c * (physicalResidueMean (g c) lo N M u).re := by
  exact exists_residue_slice_of_rectangular_scalar_family outer source parent H h g
    epsilon level budget D anchor parLo parHi hpar (8 * ((d : ℝ) + 1) * (p + 1))
    htransfer productive (canonicalScalarFamilyMass d (Fintype.card C) hp hcard hmass) hproductive

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

namespace ResidueBoxSlice
variable {J : Type*} [Fintype J] [decJ : DecidableEq J] {N : J → ℕ} {q : ℕ}

noncomputable def scalarParameterEquiv (S : ResidueBoxSlice N q) :
    (∀ j, Finset.Ico (0 : ℤ) (S.length j : ℤ)) ≃ (∀ j, Fin (S.length j)) where
  toFun x j := ⟨(x j).val.toNat, by
    have := Finset.mem_Ico.mp (x j).property
    omega⟩
  invFun t j := ⟨((t j).val : ℤ), by
    exact Finset.mem_Ico.mpr ⟨Int.natCast_nonneg _, by exact_mod_cast (t j).isLt⟩⟩
  left_inv x := by
    funext j
    apply Subtype.ext
    have := (Finset.mem_Ico.mp (x j).property).1
    exact Int.toNat_of_nonneg this
  right_inv t := by
    funext j
    apply Fin.ext
    simp

theorem scalarParameterEquiv_point (S : ResidueBoxSlice N q)
    (x : ∀ j, Finset.Ico (0 : ℤ) (S.length j : ℤ)) :
    (S.fullSlicePointInIntegerBox (S.scalarParameterEquiv x)).val =
      fun j => (S.start j : ℤ) + (q : ℤ) * (x j).val := by
  funext j
  have hj := (Finset.mem_Ico.mp (x j).property).1
  simp only [fullSlicePointInIntegerBox, point, scalarParameterEquiv,
    Equiv.coe_fn_mk, Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg hj]

theorem rectangularScalarDiscrepancy_eq_fullSliceLaw
    {X : Type*} [Fintype X] (S : ResidueBoxSlice N q) (hlen : ∀ j, 0 < S.length j)
    (parent : X → ℤ) (H : X → ℕ) (h g : (X → ℤ) → ℂ)
    (epsilon level : ℝ) (frame : Option J × X → ℤ)
    (hinside : ∀ u : integerBox N,
      smoothAffineSample u.val frame ∈ translatedIntegerBox parent H) :
    rectangularScalarDiscrepancy parent H h g epsilon level q
      (fun j => (S.start j : ℤ)) 0 (fun j => (S.length j : ℤ))
      (fun j => by change (0 : ℤ) < (S.length j : ℤ); exact_mod_cast hlen j) frame =
    (S.fullSliceLaw hlen).mean (fun u =>
      (h (smoothAffineSample u.val frame)).re -
        (1 + epsilon) * level * (g (smoothAffineSample u.val frame)).re) := by
  have hdec : decJ = Classical.decEq J := Subsingleton.elim _ _
  subst decJ
  rw [rectangularScalarDiscrepancy, integerBoxUniformWeights_mean, S.fullSliceLaw_mean]
  apply Fintype.expect_equiv S.scalarParameterEquiv
  intro x
  rw [S.scalarParameterEquiv_point]
  have hi := hinside (S.fullSlicePointInIntegerBox (S.scalarParameterEquiv x))
  rw [S.scalarParameterEquiv_point] at hi
  rw [realZeroExtendFinset_on _ _ hi, realZeroExtendFinset_on _ _ hi]

end ResidueBoxSlice
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical
universe u v

theorem exists_unconditioned_trimmed_slice_family (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → 2 ≤ Fintype.card J →
    (Fintype.card J : ℝ) ≤ Real.exp P0 →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ {κ : Type*} [Fintype κ] (_k0 : J) (D : κ → ℕ)
      (anchor parLo parHi : κ → J → ℤ) (hpar : ∀ r j, parLo r j < parHi r j),
    (∀ r, 0 < D r) → (∀ r, (D r : ℝ) ≤ Real.exp P0) →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ∀ (R : κ → ℕ) (parMin : κ → ℝ), (∀ r, 0 < parMin r) →
    (∀ r j, parMin r ≤ ((parHi r j - parLo r j : ℤ) : ℝ)) →
    (∀ r j, parHi r j - parLo r j ≤ (R r : ℤ)) →
    (∀ r, (R r : ℝ) ≤ Cwidth * parMin r) → (∀ r, c * L ≤ parMin r) →
    (∀ r j, |((anchor r j + (D r : ℤ) * parLo r j : ℤ) : ℝ) / L| ≤ C) →
    (∀ r j, |((anchor r j + (D r : ℤ) * parHi r j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (width : Option J × I → ℝ) (hwidth : ∀ z, 0 < width z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (margin : I → ℕ) (hmargin : ∀ i, 2 * margin i < N i),
    (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1 / 2 →
    (∀ i, width (none,i) ≤ (margin i : ℝ)) →
    (∀ z : J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some z.1,z.2)) →
    4 * ((Fintype.card (J × I) : ℝ) + 1) ≤ p →
    let sourceLo := jointFrameSourceLo width
    let sourceHi := jointFrameSourceHi N width
    ∀ (origin : Option J × I → ℤ),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    scalarInitialThreshold E (Fintype.card (Option J × I)) (Fintype.card I)
      (Fintype.card J) epsilon p P0 ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (Fintype.card J + 1) ≤ H i) →
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ productive : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
    (Fintype.card κ : ℝ) * Real.exp (-p) < outer.eventProbability productive →
    (∀ z, productive z → ∃ r, Real.exp (-p) <
      rectangularScalarDiscrepancy lo N h g.eval epsilon level
        (D r) (anchor r) (parLo r) (parHi r) (hpar r)
        (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) →
    ∃ (cellLo : I → ℤ) (cellN : I → ℕ) (M : ℕ) (a : I → ℤ),
      0 < M ∧ PhysicalSubbox lo N cellLo cellN ∧
      ResidueSliceLogCostLE N cellLo cellN M a budget ∧
      Nonempty (IntegerResidueBox cellLo (fun i => cellLo i + cellN i) (fun _ => (M : ℤ)) a) ∧
      (∀ i, 0 < residueIndexLength (cellLo i) (cellLo i + cellN i) M (a i)) ∧
      Real.exp (-budget) < (physicalResidueMean h cellLo cellN M a).re -
        level * (physicalResidueMean g.eval cellLo cellN M a).re := by
  obtain ⟨E, hE, htransfer⟩ := exists_unconditioned_trimmed_threshold_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    κ _ k0 D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim sourceLo sourceHi origin
    hwinScale hW hsourceLo hsourceHi hbudget hLexp hHexp
    outer productive hmass hproductive
  obtain ⟨r, cellLo, cellN, M, a, hM, hcell, hcost, hne, hlen, hscore⟩ :=
    exists_residue_slice_of_rectangular_scalar_family outer
      (fun z i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) lo N
      (fun _ : κ => h) (fun _ : κ => g.eval)
      (fun _ => epsilon) (fun _ => level) (fun _ => budget)
      D anchor parLo parHi hpar p (fun r hnoincrement => by
        exact htransfer nilmanifold p epsilon P0 level budget
          hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile
          g hcomplexity k0 (D r) (anchor r) (parLo r) (parHi r) (hpar r) (hD r) (hDlog r)
          L C B A K c Cwidth hC hB hA hK hc hCwidth
          hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
          (R r) (parMin r) (hparMin r) (hparSide r) (hparWidth r) (hwidthRatio r)
          (hrelative r) (hleft r) (hright r)
          width hwidth hZ margin hmargin hloss hroot hscale hpDim
          origin hwinScale hW hsourceLo hsourceHi hbudget hLexp hHexp)
      productive hmass hproductive
  exact ⟨cellLo, cellN, M, a, hM, hcell, hcost, hne, hlen, hscore⟩

end Erdos3

end

end OAI
