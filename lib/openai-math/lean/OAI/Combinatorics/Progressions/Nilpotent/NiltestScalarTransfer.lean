import OAI.Combinatorics.Progressions.Dynamics.ScalarDoublingBudget
import OAI.Combinatorics.Progressions.Estimates.BaselineNoIncrementTree
import OAI.Combinatorics.Progressions.Estimates.InitialReplacementMeshWidths
import OAI.Combinatorics.Progressions.Estimates.OrdinaryMeshMarginals
import OAI.Combinatorics.Progressions.Estimates.ScalarInputLogFactor
import OAI.Combinatorics.Progressions.Estimates.ScalarWindowPartitions
import OAI.Combinatorics.Progressions.Geometry.ScalarBoxGeometry
import OAI.Combinatorics.Progressions.Lattices.AffineMeshScalarTail
import OAI.Combinatorics.Progressions.Lattices.AffineNormalizedScales
import OAI.Combinatorics.Progressions.Lattices.AffinePrecisionBudget
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineSecondaryMesh
import OAI.Combinatorics.Progressions.Sampling.PhysicalGridCostFromLogs

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_affine_reference_comparison (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype σ] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p ε L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < ε → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card σ : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card σ : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × σ) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : σ => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (parameterA : J → ℤ),
    ((affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail ε L T : ℕ) : ℝ) ≤ p →
    ∀ (parent lo a : σ → ℤ) (H N : σ → ℕ), PhysicalSubbox parent H lo N →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ResidueSliceLogCostLE H lo N 1 a p →
    ∀ (h : (σ → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval parent H ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (hne : Nonempty (IntegerResidueBox lo (fun k => lo k + N k) (fun _ => (1 : ℤ)) a))
      (sourceLo sourceA : Option J × σ → ℤ) (sourceN : Option J × σ → ℕ)
      (hneSource : Nonempty (IntegerResidueBox sourceLo (fun k => sourceLo k + sourceN k)
        (fun _ => (1 : ℤ)) sourceA)) (sourceWeight : (Option J × σ → ℤ) → ℝ),
    (∀ z ∈ translatedIntegerBox sourceLo sourceN, 0 ≤ sourceWeight z ∧ sourceWeight z ≤ 1) →
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C totalShell modLog
    (∀ k, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C totalShell modLog dimLog)) ≤ (N k : ℝ)) →
    (∀ k, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × σ)) (Fintype.card σ)
      ε L T C totalShell modLog sourceDimLog) ≤ (sourceN k : ℝ)) →
    productTruncatedPairing (affinePeriodProductCoupling (σ := σ) (fun i => prime i ^ power i) D parameterA)
      (lowDegreeCoordinateSets ι B)
      (residuePrimeCoordinateDensity sourceLo sourceN 1 sourceA hneSource (fun i => prime i ^ power i) sourceWeight)
      (fun z => residuePrimeCoordinateDensity lo N 1 a hne (fun i => prime i ^ power i) (fun x => (h x).re) z -
        (1 + ε) * level * residuePrimeCoordinateDensity lo N 1 a hne (fun i => prime i ^ power i) (fun x => (g.eval x).re) z) ≤
      100 * (1 + ε) * Real.exp (-T / 2) + (1 + ε) * totalShell := by
  obtain ⟨E, hE, htreeExists⟩ := exists_baseline_comparison_tree.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p ε L T C totalShell modLog dimLog sourceDimLog level
    hp hε hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hσ hcount hdim hsourceDim hJ g hcomplexity prime power _ hprime hinj hmoduli
    D parameterA hmaskCard hr parent lo a H N hbox hunit hcost h hh hupper
    hne sourceLo sourceA sourceN hneSource sourceWeight hw A B hside hsourceSide
  let shell := adaptiveAffineShell A (Fintype.card (Option J × σ)) (Fintype.card σ) ε L T C totalShell modLog
  have hδ : 0 < affineStabilityTolerance T := Real.exp_pos _
  have hδinv : (affineStabilityTolerance T)⁻¹ ≤ Real.exp p := by
    simpa only [affineStabilityTolerance, Real.exp_neg, inv_inv] using Real.exp_le_exp.mpr hTP
  have hprimeP (i) : ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p :=
    (hmoduli i).trans (Real.exp_le_exp.mpr hmodLogP)
  have hlarge (k : σ) : Real.exp ((p + 2) ^ E) ≤ (H k : ℝ) :=
    ((Real.exp_le_exp.mpr (le_max_left _ _)).trans (hside k)).trans
      (by exact_mod_cast hbox.length_le k)
  have hlevel : 0 ≤ level := (Real.exp_pos (-L)).le.trans hlower
  obtain ⟨tree, depth, hdepth, htree⟩ := htreeExists nilmanifold p (affineStabilityTolerance T)
    hp hσ hδ hδinv g hcomplexity prime power hprime hinj hprimeP
    (affineSamplerPrimeMask prime (ε / (2 + ε)) (affineComparisonScale ε L T C) 1 1 D)
    (affineRemovalDepth T + affineComparisonTail ε L T) hmaskCard hr
    parent H N lo a 1 (by decide) hbox hunit hcost hlarge h level
    (affineIncrementTolerance L T) hlevel hupper
  have hA : depth ≤ A := by
    exact_mod_cast hdepth.trans (Nat.le_ceil ((p + 2) ^ E))
  have hB := adaptiveAffineCutoff_bounds A (Fintype.card (Option J × σ)) (Fintype.card σ)
    ε L T C totalShell modLog
  have hshell : 0 < shell := adaptiveAffineShell_pos A (Fintype.card (Option J × σ))
    (Fintype.card σ) ε L T C modLog htotal
  have hsideRaw (k : σ) :
      Real.exp (modLog * A + affineComparisonLengthLog B ε L T C modLog dimLog + 2) ≤ (N k : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hside k)
  have hallocation := (adaptiveAffineShell_allocation A (Fintype.card (Option J × σ))
    (Fintype.card σ) ε L T C totalShell modLog).le
  have hcomparison := normalized_adaptive_affine_comparison lo a N hne sourceLo sourceA sourceN hneSource
    h g.eval sourceWeight (fun z hz => (hunit z hz).2) hh hw hε hL hT hC hshell hlower hlevel2
    hmodLog hdimLog hsourceDimLog hmoduli hcount hdim hsourceDim prime power hprime (fun _ => rfl)
    hinj hJ D parameterA tree (fun _ _ => 0) (fun _ _ => 0) htree hA hB.1 hB.2 hsideRaw hsourceSide hallocation
  have hP := (affineComparisonScale_bounds (ε := ε) hL hT hC).1
  have heta := affineComparisonAccuracy_bounds (level := Real.exp (-L)) B hP hL hT le_rfl
  exact hcomparison.trans (normalized_affine_error_le hε.le hT hlevel hlevel2 heta.1.le heta.2.1.le
    hshell.le (adaptiveAffineShell_le A (Fintype.card (Option J × σ)) (Fintype.card σ) hL hT hC hmodLog htotal.le))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_mesh_reference_bounds (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < epsilon → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card I : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × I) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (anchor : J → ℤ),
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon)) (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ p →
    ∀ (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)),
    (∀ i c, (P i).step c = 1) → ∀ (hPpos : ∀ i c, 0 < (P i).length c),
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    (∀ i c, Real.exp (-p) * (N i : ℝ) ≤ ((P i).length c : ℝ)) →
    ∀ (h : (I → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ)
      (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat),
    (∀ i cs, (S i).step cs = 1) → ∀ (hSpos : ∀ i cs, 0 < (S i).length cs),
    ∀ sourceWeight : (Option J × I → ℤ) → ℝ,
    (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ sourceWeight (fun i => (z i).val) ∧ sourceWeight (fun i => (z i).val) ≤ 1) →
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog
    (∀ i c, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
        epsilon L T C totalShell modLog dimLog)) ≤ ((P i).length c : ℝ)) →
    (∀ i cs, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog sourceDimLog) ≤ ((S i).length cs : ℝ)) →
    ∀ (cs : ∀ i, (S i).Label) (c : ∀ i, (P i).Label),
    productTruncatedPairing (affinePeriodProductCoupling (σ := I) (fun i => prime i ^ power i) D anchor)
      (lowDegreeCoordinateSets ι B)
      (residuePrimeCoordinateDensity (fun i => intervalCellLower (sourceLo i) (S i) (cs i))
        (fun i => (S i).length (cs i)) 1 (fun _ => 0)
        (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs)
        (fun i => prime i ^ power i) sourceWeight)
      (fun x => residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun z => (h z).re) x -
        (1 + epsilon) * level * residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun z => (g.eval z).re) x) ≤
      100 * (1 + epsilon) * Real.exp (-T / 2) + (1 + epsilon) * totalShell := by
  obtain ⟨E, hE, href⟩ := exists_niltest_affine_reference_comparison.{u,v,w} s
  refine ⟨E, hE, ?_⟩
  intro ι I V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power _ hprime hinj hmoduli
    D anchor hmask hdepth lo N P hPstep hPpos hunit hwidth h hh hupper
    sourceLo sourceHi S hSstep hSpos sourceWeight hw A B hside hsourceSide cs c
  have hsubset := physicalBoxCell_subset lo N P hPstep hPpos c
  have hwcell (z) (hz : z ∈ translatedIntegerBox
      (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun i => (S i).length (cs i))) :
      0 ≤ sourceWeight z ∧ sourceWeight z ≤ 1 := by
    obtain ⟨x, _, hx⟩ := integerBoxMesh_cell_realize sourceLo sourceHi S hSstep hSpos cs z hz
    simpa only [hx] using hw x
  exact href nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power hprime hinj hmoduli
    D anchor hmask hdepth lo (fun i => intervalCellLower (lo i) (P i) (c i)) (fun _ => 0)
    N (fun i => (P i).length (c i)) (physicalBoxCell_subbox lo N P hPstep hPpos c)
    (fun z hz => hunit z (hsubset hz)) (physicalBoxCell_log_cost lo N P c p (fun i => hwidth i (c i)))
    h (fun z hz => hh z (hsubset hz)) hupper (physicalBoxCell_nonempty lo N P hPpos c)
    (fun i => intervalCellLower (sourceLo i) (S i) (cs i)) (fun _ => 0) (fun i => (S i).length (cs i))
    (physicalBoxCell_nonempty sourceLo (fun i => (sourceHi i - sourceLo i).toNat) S hSpos cs)
    sourceWeight hwcell (fun i => hside i (c i)) (fun i => hsourceSide i (cs i))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_mesh_scalar_transfer (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon L T C totalShell modLog dimLog sourceDimLog level : ℝ),
    2 ≤ p → 0 < epsilon → 0 ≤ L → 0 ≤ T → 0 ≤ C → 0 < totalShell →
    0 ≤ modLog → modLog ≤ p → 0 ≤ dimLog → 0 ≤ sourceDimLog → T + 4 ≤ p →
    Real.exp (-L) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → (Fintype.card ι : ℝ) ≤ Real.exp C →
    (Fintype.card I : ℝ) ≤ Real.exp dimLog →
    (Fintype.card (Option J × I) : ℝ) ≤ Real.exp sourceDimLog → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp modLog) →
    ∀ (D : ℕ) (anchor : J → ℤ),
    ((affineSamplerPrimeMask prime (epsilon / (2 + epsilon)) (affineComparisonScale epsilon L T C) 1 1 D).card : ℝ) ≤ p →
    ((affineRemovalDepth T + affineComparisonTail epsilon L T : ℕ) : ℝ) ≤ p →
    ∀ (lo : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i)),
    (∀ i c, (P i).step c = 1) → ∀ (hPpos : ∀ i c, 0 < (P i).length c),
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    (∀ i c, Real.exp (-p) * (N i : ℝ) ≤ ((P i).length c : ℝ)) →
    ∀ (h : (I → ℤ) → ℂ),
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N ((p + 2) ^ E) level (affineIncrementTolerance L T) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ)
      (S : ∀ i, FiniteProgressionPartition (sourceHi i - sourceLo i).toNat),
    (∀ i cs, (S i).step cs = 1) → ∀ (_hSpos : ∀ i cs, 0 < (S i).length cs),
    ∀ (hsource : ∀ i, sourceLo i < sourceHi i),
    let A := ⌈(p + 2) ^ E⌉₊
    let B := adaptiveAffineCutoff A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog
    (∀ i c, Real.exp (max ((p + 2) ^ E)
      (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
        epsilon L T C totalShell modLog dimLog)) ≤ ((P i).length c : ℝ)) →
    (∀ i cs, Real.exp (adaptiveAffineSideLog A (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon L T C totalShell modLog sourceDimLog) ≤ ((S i).length cs : ℝ)) →
    ∀ (paramLo paramHi : J → ℤ) (hparam : ∀ j, paramLo j < paramHi j)
      (paramPartition : ∀ j, FiniteProgressionPartition (paramHi j - paramLo j).toNat),
    (∀ j c, (paramPartition j).step c = 1) →
    ∀ (hTpos : ∀ j c, 0 < (paramPartition j).length c),
    ∀ (etaParam etaSite beta accuracy : ℝ), 0 ≤ etaParam → 0 ≤ etaSite →
    ∀ (_hcloseParam : ∀ ct : (∀ j, (paramPartition j).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := J) (fun i => prime i ^ power i))
        (residuePrimeCoordinateDensity (fun j => intervalCellLower (paramLo j) (paramPartition j) (ct j))
          (fun j => (paramPartition j).length (ct j)) 1 (fun _ => 0)
          (physicalBoxCell_nonempty paramLo (fun j => (paramHi j - paramLo j).toNat) paramPartition hTpos ct)
          (fun i => prime i ^ power i) (fun _ => 1)) etaParam B)
    (_hcloseSite : ∀ c : (∀ i, (P i).Label),
      ProductMarginalsClose (primeCoordinateReference (σ := I) (fun i => prime i ^ power i))
        (residuePrimeCoordinateDensity (fun i => intervalCellLower (lo i) (P i) (c i))
          (fun i => (P i).length (c i)) 1 (fun _ => 0) (physicalBoxCell_nonempty lo N P hPpos c)
          (fun i => prime i ^ power i) (fun _ => 1)) etaSite B)
    (_hbad : ((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).eventProbability
      (physicalMeshCrossing lo N P
        (fun tz => (integerBoxMesh sourceLo sourceHi S tz.2, integerBoxMesh paramLo paramHi paramPartition tz.1))
        (fun tz => smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val))) ≤ beta)
    (_heh : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos (fun i => prime i ^ power i) B (fun z => (h z).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (_heg : ∀ w : (Option J × I → ℤ) → ℝ, (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
      0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights paramLo paramHi hparam).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
      (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hPpos (fun i => prime i ^ power i) B (fun z => (g.eval z).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤ accuracy)
    (pTarget dominationLog : ℝ)
    (outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)))
    (_hdom : ∀ z, outer.weight z ≤ Real.exp dominationLog *
      (integerBoxUniformWeights sourceLo sourceHi hsource).weight z)
    (_herror : (100 * (1 + epsilon) * Real.exp (-T / 2) + (1 + epsilon) * totalShell) + (1 + ((1 + epsilon) * level)) * ((etaParam + beta) * residueTruncationCap ι B etaSite + accuracy) ≤
      Real.exp (-(2 * pTarget + dominationLog)) / 2),
    outer.eventProbability (fun z => Real.exp (-pTarget) <
      (integerBoxUniformWeights paramLo paramHi hparam).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        ((1 + epsilon) * level) * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤
      Real.exp (-pTarget) := by
  obtain ⟨E, hE, href⟩ := exists_niltest_mesh_reference_bounds.{u,v,w} s
  refine ⟨E, hE, ?_⟩
  intro ι I V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power _ hprime hinj hmoduli
    D anchor hmask hdepth lo N P hPstep hPpos hunit hwidth h hh hupper
    sourceLo sourceHi S hSstep hSpos hsource A B hside hsourceSide
    paramLo paramHi hparam paramPartition hTstep hTpos etaParam etaSite beta accuracy
    hetaParam hetaSite hcloseParam hcloseSite hbad heh heg pTarget dominationLog outer hdom herror
  apply affine_mesh_scalar_tail lo N P hPstep hPpos sourceLo sourceHi hsource
    S hSstep hSpos paramLo paramHi hparam paramPartition hTstep hTpos D anchor
    (fun i => prime i ^ power i) B (fun z => (h z).re) (fun z => (g.eval z).re)
    hh (fun z hz => (hunit z hz).2) hetaParam hetaSite
    (mul_nonneg (by linarith) ((Real.exp_pos (-L)).le.trans hlower))
    (by positivity) hcloseParam hcloseSite ?_ hbad heh heg pTarget dominationLog outer hdom herror
  intro sourceWeight hw cs c
  exact href nilmanifold p epsilon L T C totalShell modLog dimLog sourceDimLog level
    hp hepsilon hL hT hC htotal hmodLog hmodLogP hdimLog hsourceDimLog hTP hlower hlevel2
    hI hcount hdim hsourceDim hJ g hcomplexity prime power hprime hinj hmoduli
    D anchor hmask hdepth lo N P hPstep hPpos hunit hwidth h hh hupper
    sourceLo sourceHi S hSstep hSpos sourceWeight hw hside hsourceSide cs c

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v w

theorem exists_niltest_geometric_scalar_transfer (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {I : Type u} {V : Type v} {J : Type*}
      [Fintype ι] [LinearOrder ι] [Fintype I] [Fintype J]
      [LieRing V] [LieAlgebra ℚ V] [TopologicalSpace (ℝ ⊗[ℚ] V)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d)
      (p epsilon Z U gridLog ratioLog meshLog level budget : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ Z → 0 ≤ U → 0 ≤ meshLog →
    p ≤ U → scalarTransferTail (3 * p) ≤ U → Z ≤ U →
    gridLog + ratioLog + 2 ≤ U → epsilon⁻¹ ≤ Real.exp U →
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ U → (Fintype.card (Option J × I) : ℝ) ≤ U →
    (Fintype.card J : ℝ) ≤ U → 2 ≤ Fintype.card J →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (prime power : ι → ℕ) [∀ i, NeZero (prime i ^ power i)],
    (∀ i, (prime i).Prime) → Function.Injective prime →
    (Fintype.card ι : ℝ) ≤ Real.exp Z →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp Z) →
    ∀ (D : ℕ) (anchor : J → ℤ), 0 < D → (D : ℝ) ≤ Real.exp Z →
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let Aref := ⌈(pref + 2) ^ E⌉₊
    let b := adaptiveAffineCutoff Aref (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let _beta := scalarTransferMarginalAccuracy (3 * p) (scalarTransferCapLog b Z)
    let cellLog := scalarTransferCellLog common b p Z U
    (pref + 2) ^ E ≤ budget → p + scalarTransferTail (3 * p) + 4 ≤ budget →
    scalarTransferAccuracyLog b p Z ≤ meshLog →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ)
      (rho L C B A c sourceRatio parameterRatio : ℝ),
    0 < rho → 1 ≤ L → (∀ i, 0 < H i) → 0 ≤ C → 0 ≤ B → 0 ≤ A → 0 < c →
    0 ≤ sourceRatio → 0 ≤ parameterRatio → rho⁻¹ ≤ Real.exp gridLog → A ≤ Real.exp ratioLog →
    ∀ (hsiteLarge : ∀ i, 4 ≤ rho * H i) (hsiteWhole : ∀ i, rho * H i ≤ 2 * (N i : ℝ)),
    (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ i, 4 * Real.exp (gridLog + max ((pref + 2) ^ E) cellLog) ≤ H i) →
    let P := normalizedBoxPartitions N H rho hsiteLarge hsiteWhole
    let hpos := normalizedBoxPartitions_positive N H rho hsiteLarge hsiteWhole
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z)
      (parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    (∀ i, c * H i ≤ ((sourceHi (none,i) - sourceLo (none,i) : ℤ) : ℝ)) →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    40 * (Fintype.card I : ℝ) * A / (rho * c) ≤ Real.exp meshLog →
    1 + (Fintype.card J : ℝ) * (C + B) ≤ Real.exp meshLog →
    sourceRatio ≤ Real.exp meshLog → parameterRatio ≤ Real.exp meshLog →
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      sourceRatio * ((sourceHi z - sourceLo z).toNat : ℝ)) →
    (∀ j, L / (D : ℝ) ≤ parameterRatio * ((parHi j - parLo j).toNat : ℝ)) →
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L →
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ (Fintype.card J + 1) ≤ H i) →
    (∀ w : (Option J × I → ℤ) → ℝ,
      (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
        0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights parLo parHi hpar).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
        (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hpos
          (fun i => prime i ^ power i) b (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤
        scalarTransferBaseAccuracy (3 * p)) →
    (∀ w : (Option J × I → ℤ) → ℝ,
      (∀ z : (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
        0 ≤ w (fun i => (z i).val) ∧ w (fun i => (z i).val) ≤ 1) →
      |((integerBoxUniformWeights parLo parHi hpar).prod
        (integerBoxUniformWeights sourceLo sourceHi hsource)).mean
        (fun tz => w (fun i => (tz.2 i).val) * physicalBoxResidual lo N P hpos
          (fun i => prime i ^ power i) b (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (tz.1 j).val) (fun i => (tz.2 i).val)))| ≤
        scalarTransferBaseAccuracy (3 * p)) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, href⟩ := exists_niltest_mesh_scalar_transfer.{u,v,w} s
  refine ⟨E, hE, ?_⟩
  intro ι I V J _ _ _ _ _ _ _ _ _ _ d nilmanifold p epsilon Z U gridLog ratioLog meshLog level budget
    hp hepsilon hepsilon1 hZ hU hmesh hpU htailU hZU hgridBudget hepsInv hlower hlevel
    hI hsourceDim hJdim hJ g hcomplexity prime power _ hprime hinj hcount hmoduli D anchor hD hDlog
    pref common Aref b beta cellLog hbudget hprecision haccMesh lo N H rho L C B A c sourceRatio parameterRatio
    hrho hL hH hC hB hA hc hsRatio hpRatio hrhoInv hAlog hsiteLarge hsiteWhole hsize hfirstScale
    P hpos hunit h hh hupper sourceLo sourceHi hsource parLo parHi hpar
    hbaseWidth hparamLo hparamHi hsourceLo hsourceHi hboundary hmovement hsLog hpLog hsourceWidth hparameterWidth
    hLscale hHscale heh heg outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hbase : 0 < scalarTransferBaseAccuracy (3 * p) := Real.exp_pos _
  have hbaseInv : (scalarTransferBaseAccuracy (3 * p))⁻¹ ≤ Real.exp U := by
    simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
    apply Real.exp_le_exp.mpr
    unfold scalarTransferTail at htailU
    linarith
  have hrefInput := affineReferenceInput_bounds epsilon hU
  have hmask := affineReferenceInput_mask_and_depth prime hprime hinj D hD hepsilon hepsilon1 hU
    hp0 hT hZ hpU htailU hZU hepsInv (hDlog.trans (Real.exp_le_exp.mpr hZU))
  have hcommon : 0 ≤ common := (affineCommonReferenceBudget_bounds hE epsilon hU).1
  have hlogs := scalarTransferAllocatedLogs_bounds b hcommon hp0 hZ hU
  have hcell : 0 ≤ cellLog := hlogs.2.2.1
  have hacc : 0 ≤ scalarTransferAccuracyLog b p Z := hlogs.2.1
  have hbeta : 0 < beta := Real.exp_pos _
  have hbeta1 : beta ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hacc)
  have hbetaInv : beta⁻¹ ≤ Real.exp meshLog := by
    change (Real.exp (-scalarTransferAccuracyLog b p Z))⁻¹ ≤ _
    rw [Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr haccMesh
  have hside := adaptiveAffineSideLog_reference_bound hE hepsilon hepsilon1 hU hp0 hT hZ hZ
    hpU htailU hZU hZU le_rfl hsourceDim hI hepsInv hbase hbaseInv
  have hsideCell : adaptiveAffineSideLog Aref (Fintype.card (Option J × I)) (Fintype.card I)
      epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z U ≤ cellLog :=
    hside.trans hlogs.2.2.2.1
  have hpair : Pairwise (fun i j => (prime i ^ power i).Coprime (prime j ^ power j)) := by
    intro i j hij
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hprime i) (hprime j)).mpr (fun h => hij (hinj h)))
  have hUexp : U ≤ Real.exp U := by linarith [Real.add_one_le_exp U]
  have hdimi : (Fintype.card I : ℝ) ≤ Real.exp U := hI.trans hUexp
  have hdimj : (Fintype.card J : ℝ) ≤ Real.exp U := hJdim.trans hUexp
  have hdimsource : (Fintype.card (Option J × I) : ℝ) ≤ Real.exp U := hsourceDim.trans hUexp
  have hfirst (i) (ci) : Real.exp (max ((pref + 2) ^ E) cellLog) ≤ ((P i).length ci : ℝ) :=
    normalizedBoxPartitions_exp_lengths N H rho gridLog _ hrho hrhoInv hfirstScale hsiteLarge hsiteWhole i ci
  have hcellSite (i) (ci) : Real.exp cellLog ≤ ((P i).length ci : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans (hfirst i ci)
  have hscales := affineNormalizedScales_lower (J := J) H hL hD (by omega : 1 ≤ Fintype.card J + 1)
    hDlog hLscale hHscale
  obtain ⟨S, T, hSstep, hSpos, hTstep, hTpos, hSlength, hTlength, hbad⟩ :=
    exists_allocated_affine_secondary_mesh sourceLo sourceHi hsource parLo parHi anchor hpar D hD
      lo N H (by linarith : 0 < L) hH hC hB hA hc hrho hsRatio hpRatio hmesh hcell hbeta
      hsiteLarge hsiteWhole hsize hbaseWidth hparamLo hparamHi hsourceLo hsourceHi
      hboundary hmovement hsLog hpLog hbetaInv hsourceWidth hparameterWidth hscales.2.1 hscales.2.2
  have hsiteClose := ordinaryMesh_marginals_of_lengths lo N P hpos (fun i => prime i ^ power i)
    hpair b Z U 0 cellLog 1 hZ le_rfl (by norm_num) hmoduli hdimi
    (by simpa only [add_zero] using hlogs.2.2.2.2.2) hcellSite
  have hparamClose := ordinaryMesh_marginals_of_lengths parLo (fun j => (parHi j - parLo j).toNat)
    T hTpos (fun i => prime i ^ power i) hpair b Z U (scalarTransferAccuracyLog b p Z) cellLog beta
    hZ hbeta1 le_rfl hmoduli hdimj hlogs.2.2.2.2.1 hTlength
  have hcap := residueTruncationCap_le_exp b hZ (by norm_num : (0 : ℝ) ≤ 1) le_rfl hcount
  have hcap0 := residueTruncationCap_nonneg ι b (by norm_num : (0 : ℝ) ≤ 1)
  have herror := scalarTransfer_combined_error_le (targetLog := 3 * p) hepsilon.le hepsilon1
    ((Real.exp_pos (-p)).le.trans hlower) hlevel hcap0 hcap
  apply href nilmanifold pref epsilon p (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z U U level
    hrefInput.1 hepsilon hp0 hT hZ hbase hZ (hZU.trans hrefInput.2.1) hU hU hmask.2.2 hlower hlevel
    (hI.trans hrefInput.2.1) hcount hdimi hdimsource hJ g
    (hcomplexity.mono (hpU.trans hrefInput.2.1)) prime power hprime hinj hmoduli D anchor hmask.1 hmask.2.1
    lo N P (normalizedBoxPartitions_step _ _ _ _ _) hpos hunit
    (normalized_physical_cell_width_log_budget N H rho A gridLog ratioLog pref
      (fun i => (hH i).le) hrho hA hsiteLarge hsiteWhole hsize hrhoInv hAlog
      (hgridBudget.trans hrefInput.2.1)) h hh (hupper.from_exponential_budget hbudget hprecision)
    sourceLo sourceHi S hSstep hSpos hsource ?_ ?_
    parLo parHi hpar T hTstep hTpos beta 1 beta (scalarTransferBaseAccuracy (3 * p))
    hbeta.le (by norm_num) hparamClose hsiteClose hbad heh heg p p outer hdom ?_
  · intro i ci
    exact (Real.exp_le_exp.mpr (max_le_max le_rfl hsideCell)).trans (hfirst i ci)
  · intro i ci
    exact (Real.exp_le_exp.mpr hsideCell).trans (hSlength i ci)
  · simpa only [beta, scalarTransferCapLog, b, Aref, show 2 * p + p = 3 * p by ring] using herror

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_initial_scalar_transfer (s : ℕ) :
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
    ∀ (k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ L → 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    (pref + 2) ^ E ≤ budget → p + scalarTransferTail (3 * p) + 4 ≤ budget →
    Real.exp (Z + P0) ≤ L →
    (∀ i, Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k0}) b Z + 16) *
      L ^ (d + 1) ≤ H i) →
    (∀ i, 4 * Real.exp (G + max ((pref + 2) ^ E) cellLog) ≤ H i) →
    4 * Real.exp (4 * meshLog + 18 + cellLog + Z) ≤ L →
    (∀ i, 4 * Real.exp (4 * meshLog + 18 + cellLog) * L ^ (d + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, hgeom⟩ := exists_niltest_geometric_scalar_transfer.{u,v,0} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hL hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hprecision hLlog hsizeExp hfirstScale hLmesh hHmesh outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hpP0 : p ≤ P0 := by linarith
  have hP0exp : P0 ≤ Real.exp P0 := by linarith [Real.add_one_le_exp P0]
  have hnlog : (n : ℝ) ≤ Real.exp P0 := hnP.trans (hpP0.trans hP0exp)
  have hZdata := replacementCommonInputLog_bounds m n d hP0
  have hZ : 0 ≤ Z := hZdata.1
  have hP0Z : P0 ≤ Z := hZdata.2.1
  obtain ⟨hU, hZU, hGU, hP0U, hmU, hnU, hdU, hTU, hpU⟩ := scalarInitialReferenceInput_bounds m n d hp0 hP0
  have hG : 0 ≤ G := by
    have hcoef := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]
    linarith
  have hbase : 0 < scalarTransferBaseAccuracy (3 * p) := Real.exp_pos _
  have hbaseInv : (scalarTransferBaseAccuracy (3 * p))⁻¹ ≤ Real.exp P0 := by
    simp only [scalarTransferBaseAccuracy, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr htarget
  have hepsU := hepsInv.trans (Real.exp_le_exp.mpr hP0U)
  have hbaseU := hbaseInv.trans (Real.exp_le_exp.mpr hP0U)
  have hT : 0 ≤ scalarTransferTail (3 * p) := by unfold scalarTransferTail; positivity
  have hb := adaptiveAffineCutoff_reference_bounds hE hepsilon hepsilon1 hU hp0 hT hZ hZ
    hpU hTU hZU hZU hmU hnU hepsU hbase hbaseU
  have hdegree : 2 * Z ≤ (b : ℝ) := (mul_le_mul_of_nonneg_left hZU (by norm_num)).trans hb.1
  let tol := weightedReplacementTolerance ((3 * K) ^ m) ((2 : ℝ) ^ (n + 1) * A ^ n)
    (scalarTransferBaseAccuracy (3 * p))
  let Q := D * integerBoxGcdCutoff d Cwidth tol
  let κ := integerBoxRetainedGap d D c tol
  let rho := physicalPairGridAccuracy n k0 C κ A tol
  obtain ⟨htol, _, _, _, hQlog, _⟩ := replacement_selected_parameter_bounds m n d D hP0 hK hA hCwidth hc hbase hD
    hDlog hKlog hAlog hWidthlog hcinv hbaseInv
  have hrho := physicalPairGridAccuracy_spec n k0 C κ hA htol
  have hrhoInvSmall := selectedPhysicalGrid_inverse_le_exp m n k0 D hP0 hK hA
    (zero_le_one.trans hC) hCwidth hc hbase hD hnlog hJlog hDlog hKlog hAlog hClog hWidthlog hcinv hbaseInv hprofile
  have hsmall : physicalPairCoefficientLog n (Fintype.card {j : J // j ≠ k0}) Z ≤
      physicalPairCoefficientLog n d Z :=
    physicalPairCoefficientLog_mono_dimension n (Fintype.card_subtype_le _) hZ
  have hrhoInv : rho⁻¹ ≤ Real.exp G := hrhoInvSmall.trans (Real.exp_le_exp.mpr (by dsimp only [G]; linarith))
  have hcommon : 0 ≤ common := (affineCommonReferenceBudget_bounds hE epsilon hU).1
  have hlogs := scalarTransferAllocatedLogs_bounds b hcommon hp0 hZ hU
  have hcell : 0 ≤ cellLog := hlogs.2.2.1
  have hacc : 0 ≤ scalarTransferAccuracyLog b p Z := hlogs.2.1
  have hmeshBounds := scalarMeshLog_bounds hG (by linarith : 0 ≤ P0 + 1) hacc
  have hH (i) : 0 < H i :=
    (mul_pos (Real.exp_pos _) (pow_pos (by linarith : 0 < L) (d + 1))).trans_le (hsizeExp i)
  have hlarge (i) : 4 ≤ rho * H i :=
    normalizedMesh_scale_large hrho.1 hrhoInv (hcell.trans (le_max_right _ _)) (hfirstScale i)
  have hwhole (i) : rho * H i ≤ 2 * (N i : ℝ) :=
    ((mul_le_mul_of_nonneg_right hrho.2.1 (hH i).le).trans_eq (one_mul _)).trans (hupper i)
  have hwidths := initialReplacement_mesh_widths sourceLo sourceHi parLo parHi hsource hpar H
    (zero_le_one.trans hL) hK hc hD hwinScale (fun j => hrelative.trans (hparSide j))
  have hcSource : 0 < (K + 1)⁻¹ := inv_pos.mpr (by positivity)
  have hPup : Real.exp P0 ≤ Real.exp (P0 + 1) := Real.exp_le_exp.mpr (by linarith)
  have hcSourceLog : ((K + 1)⁻¹)⁻¹ ≤ Real.exp (P0 + 1) := by
    simpa only [inv_inv, add_comm] using one_add_le_exp_succ hP0 hKlog
  have hboundary := scalarMesh_boundary_bound (Nat.cast_nonneg n) hA hrho.1 hcSource hG
    (by linarith : 0 ≤ P0 + 1) hacc (hnlog.trans hPup) (hAlog.trans hPup) hrhoInv hcSourceLog
  have hmovement := scalarMesh_movement_bound (zero_le_one.trans hC) hB hG
    (by linarith : 0 ≤ P0 + 1) hacc (hJlog.trans hPup) (hClog.trans hPup) (hBlog.trans hPup)
  have hPMesh : P0 ≤ meshLog := (by linarith : P0 ≤ P0 + 1).trans hmeshBounds.2.1
  have hDlogZ := hDlog.trans (Real.exp_le_exp.mpr hP0Z)
  have hprimeBounds := boundedPrimeFamily_log_bounds Q hQlog
  let : ∀ i : BoundedPrime Q, NeZero (boundedPrime Q i ^ boundedPrimeExponent Q i) :=
    fun i => ⟨(boundedPrimePower_pos Q i).ne'⟩
  apply hgeom nilmanifold p epsilon Z U G P0 meshLog level budget
    hp hepsilon hepsilon1 hZ hU hmeshBounds.1 hpU hTU hZU hGU hepsU hlower hlevel hnU hmU hdU hJ
    g hcomplexity (boundedPrime Q) (boundedPrimeExponent Q) (boundedPrime_prime Q) (boundedPrime_injective Q)
    hprimeBounds.1 hprimeBounds.2 D anchor hD hDlogZ hbudget hprecision hmeshBounds.2.2.1
    lo N H rho L C B A ((K + 1)⁻¹) K c⁻¹ hrho.1 hL hH (zero_le_one.trans hC) hB hA hcSource hK
    (inv_nonneg.mpr hc.le) hrhoInv hAlog hlarge hwhole hratio hfirstScale hunit h hh hnoincrement
    sourceLo sourceHi hsource parLo parHi hpar hwidths.1 hleft hright hsourceLo hsourceHi hboundary hmovement
    (hKlog.trans (Real.exp_le_exp.mpr hPMesh)) (hcinv.trans (Real.exp_le_exp.mpr hPMesh))
    hwidths.2.1 hwidths.2.2 hLmesh hHmesh ?_ ?_ outer hdom
  · intro w hw
    exact initial_budget_joint_physical_replacement k0 D anchor parLo parHi hpar H hL hC hA hbase hK hc hCwidth hD
      hleft hright origin lo N b (d + 1) (by omega) (fun z => (h z).re) hh P0 hP0 hnlog hJlog
      hDlog hKlog hAlog hClog hWidthlog hcinv hbaseInv hprofile hupper hratio R parMin hparMin hJ
      hparSide hparWidth hwidthRatio hrelative sourceLo sourceHi hsource hwinScale w hw
      hLlog hdegree hsizeExp hW
  · intro w hw
    exact initial_budget_joint_physical_replacement k0 D anchor parLo parHi hpar H hL hC hA hbase hK hc hCwidth hD
      hleft hright origin lo N b (d + 1) (by omega) (fun z => (g.eval z).re) (fun z hz => (hunit z hz).2)
      P0 hP0 hnlog hJlog hDlog hKlog hAlog hClog hWidthlog hcinv hbaseInv hprofile hupper hratio
      R parMin hparMin hJ hparSide hparWidth hwidthRatio hrelative sourceLo sourceHi hsource hwinScale w hw
      hLlog hdegree hsizeExp hW

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_threshold_scalar_transfer (s : ℕ) :
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
    ∀ (_k0 : J) (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    let m := Fintype.card (Option J × I)
    let n := Fintype.card I
    let d := Fintype.card J
    let Z := replacementCommonInputLog m n d P0
    let G := 2 * physicalPairCoefficientLog n d Z + 2
    let U := scalarInitialReferenceInput m n d p P0
    let pref := affineReferenceInput epsilon U
    let common := affineCommonReferenceBudget E epsilon U
    let b := adaptiveAffineCutoff ⌈(pref + 2) ^ E⌉₊ m n epsilon p
      (scalarTransferTail (3 * p)) Z (scalarTransferBaseAccuracy (3 * p)) Z
    let cellLog := scalarTransferCellLog common b p Z U
    let meshLog := scalarMeshLog G (P0 + 1) (scalarTransferAccuracyLog b p Z)
    scalarCombinedLogThreshold n d b p P0 Z G ((pref + 2) ^ E) cellLog meshLog ≤ budget →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (d + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, hinitial⟩ := exists_niltest_initial_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hLexp hHexp outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hZ : 0 ≤ Z := (replacementCommonInputLog_bounds m n d hP0).1
  have hG : 0 ≤ G := by
    have h := (physicalPairCoefficientLog_bounds n d hZ).1
    dsimp only [G]; linarith
  have hU : 0 ≤ U := (scalarInitialReferenceInput_bounds m n d hp0 hP0).1
  have hpref : 0 ≤ pref + 2 := by
    have h := (affineReferenceInput_bounds epsilon hU).1
    dsimp only [pref]; linarith
  have hcost : 0 ≤ (pref + 2) ^ E := pow_nonneg hpref E
  have hcommon : 0 ≤ common := (affineCommonReferenceBudget_bounds hE epsilon hU).1
  have hlogs := scalarTransferAllocatedLogs_bounds b hcommon hp0 hZ hU
  have hcell : 0 ≤ cellLog := hlogs.2.2.1
  have hmesh : 0 ≤ meshLog := (scalarMeshLog_bounds hG (by linarith : 0 ≤ P0 + 1) hlogs.2.1).1
  obtain ⟨_, hcostBudget, hprecision, _, _, _, _⟩ :=
    scalarCombinedLogThreshold_bounds n d b hp0 hP0 hZ hG hcost hcell hmesh
  obtain ⟨hL, hLlog, hRsize, hFsize, hLmesh, hHmesh⟩ :=
    scalarCombinedLogThreshold_size_conditions n d b (d + 1) H hp0 hP0 hZ hG hcost hcell hmesh hbudget hLexp hHexp
  have hRother (i) : Real.exp (2 * physicalReplacementThresholdLog n (Fintype.card {j : J // j ≠ k0}) b Z + 16) *
      L ^ (d + 1) ≤ H i := by
    have hmono := physicalReplacementThresholdLog_mono_dimension n b (Fintype.card_subtype_le (fun j : J => j ≠ k0)) hZ
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
      (pow_nonneg (zero_le_one.trans hL) (d + 1))).trans (hRsize i)
  exact hinitial nilmanifold p epsilon P0 level budget hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel
    hnP hJ hJlog hprofile g hcomplexity k0 D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hL hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    (hcostBudget.trans hbudget) (hprecision.trans hbudget) hLlog hRother hFsize hLmesh hHmesh outer hdom

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_polynomial_window_transfer (s ell A0 : ℕ)
    (hell : 2 ≤ ell) (hA0 : 10 ≤ A0) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (heps0 : epsilon⁻¹ ≤ Real.exp (A0 : ℝ))
    (hell0 : (ell : ℝ) ≤ Real.exp (A0 : ℝ))
    (hprofile0 : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (A0 : ℝ)) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p level : ℝ),
    2 ≤ p →
    let P0 := (A0 : ℝ) * (p + 1)
    let budget := (p + 2) ^ C
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → Fintype.card J = ell →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (ell + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_niltest_threshold_scalar_transfer.{u,v} s
  obtain ⟨Cexp, hCexp, hpower⟩ := exists_scalarInitialThreshold_power E ell A0 hE hepsilon hepsilon1
  refine ⟨Cexp, hCexp, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p level hp P0 budget
    hlower hlevel hnP hJ g hcomplexity D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi hLexp hHexp outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hA0real : (10 : ℝ) ≤ A0 := by exact_mod_cast hA0
  have hA0P0 : (A0 : ℝ) ≤ P0 := by
    dsimp only [P0]
    nlinarith [mul_nonneg (Nat.cast_nonneg A0) hp0]
  have hP0 : 0 ≤ P0 := (Nat.cast_nonneg A0).trans hA0P0
  have htarget : 3 * p + 10 ≤ P0 := by
    have hmul := mul_le_mul_of_nonneg_right hA0real (by linarith : 0 ≤ p + 1)
    dsimp only [P0]
    nlinarith
  have hexp := Real.exp_le_exp.mpr hA0P0
  have hepsP0 : epsilon⁻¹ ≤ Real.exp P0 := heps0.trans hexp
  have hJlog : (Fintype.card J : ℝ) ≤ Real.exp P0 := by
    simpa only [hJ] using hell0.trans hexp
  have hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 := hprofile0.trans hexp
  have hJtwo : 2 ≤ Fintype.card J := by omega
  let : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  let k0 : J := Classical.choice (inferInstance : Nonempty J)
  have hm : (Fintype.card (Option J × I) : ℝ) ≤ (ell + 1 : ℝ) * p := by
    rw [Fintype.card_prod, Fintype.card_option, hJ]
    push_cast
    exact mul_le_mul_of_nonneg_left hnP (by positivity)
  have hbound : scalarInitialThreshold E (Fintype.card (Option J × I)) (Fintype.card I)
      (Fintype.card J) epsilon p P0 ≤ budget := by
    simpa only [hJ] using hpower (Fintype.card (Option J × I)) (Fintype.card I) p hp hm hnP hepsP0
  exact htransfer nilmanifold p epsilon P0 level budget hp hepsilon hepsilon1 hP0 htarget hepsP0 hlower hlevel
    hnP hJtwo hJlog hprofile g hcomplexity k0 D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi hbound hLexp
    (by simpa only [hJ] using hHexp) outer hdom

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_polynomial_box_transfer (s ell A0 : ℕ)
    (hell : 2 ≤ ell) (hA0 : 10 ≤ A0) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1)
    (heps0 : epsilon⁻¹ ≤ Real.exp (A0 : ℝ))
    (hell0 : (ell : ℝ) ≤ Real.exp (A0 : ℝ))
    (hprofile0 : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (A0 : ℝ)) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p level : ℝ),
    2 ≤ p →
    let P0 := (A0 : ℝ) * (p + 1)
    let budget := (p + 2) ^ C
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → Fintype.card J = ell →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K + 8 ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (ell + 1) ≤ H i) →
    (integerBoxUniformWeights sourceLo sourceHi hsource).eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨Cexp, hCexp, htransfer⟩ := exists_niltest_polynomial_window_transfer.{u,v} s ell A0
    hell hA0 hepsilon hepsilon1 heps0 hell0 hprofile0
  refine ⟨Cexp, hCexp, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p level hp P0 budget
    hlower hlevel hnP hJ g hcomplexity D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright sourceLo sourceHi hsource hwinScale hsourceLo hsourceHi hLexp hHexp
  have hp0 : 0 ≤ p := by linarith
  have hbudget : 4 ≤ budget := calc
    4 ≤ p + 2 := by linarith
    _ = (p + 2) ^ 1 := (pow_one _).symm
    _ ≤ (p + 2) ^ Cexp := pow_le_pow_right₀ (by linarith) (by omega)
  have hexp : 4 ≤ Real.exp budget := by linarith [Real.add_one_le_exp budget]
  have hL : 1 ≤ L := by linarith
  let scale := fun z : Option J × I => smoothPairCoefficientScale (H z.2) L z.1
  have hscale : ∀ z, 4 ≤ scale z := by
    rintro ⟨j,i⟩
    have h := affinePhysicalScales_lower hL (Real.exp_pos budget).le (by omega : 1 ≤ ell + 1) (hHexp i)
    cases j with
    | none => exact hexp.trans h.1
    | some j => exact hexp.trans h.2
  have hcount (z) : (((sourceHi z - sourceLo z).toNat : ℕ) : ℝ) =
      ((sourceHi z - sourceLo z : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hsource z).le)
  obtain ⟨S, hSstep, hSpos, hSlength, hSratio⟩ := exists_scalarWindowPartitions
    (fun z => (sourceHi z - sourceLo z).toNat) scale K
    (fun z => by have hz := hsource z; omega) hscale hK
    (fun z => by rw [hcount]; exact hwinScale z)
  let event := fun z : Option J × I → ℤ => Real.exp (-p) <
    (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
      realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (h y).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z) -
      (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (g.eval y).re)
        (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) z))
  change (integerBoxUniformWeights sourceLo sourceHi hsource).eventProbability
    (fun z => event (fun i => (z i).val)) ≤ Real.exp (-p)
  apply integerBox_partition_eventProbability_le sourceLo sourceHi hsource S hSstep hSpos event
  intro label
  let slo := fun i => intervalCellLower (sourceLo i) (S i) (label i)
  let shi := fun i => slo i + (S i).length (label i)
  have hpositive : ∀ i, slo i < shi i :=
    fun i => lt_add_of_pos_right _ (by exact_mod_cast hSpos i (label i))
  have hratio' : ∀ z : Option J × I, scale z ≤ (K + 8) * ((shi z - slo z : ℤ) : ℝ) := by
    intro z
    simpa only [shi, add_sub_cancel_left, Int.cast_natCast] using hSratio z (label z)
  have hwindow := htransfer nilmanifold p level hp hlower hlevel hnP hJ g hcomplexity
    D anchor parLo parHi hpar hD hDlog L C B A (K + 8) c Cwidth hC hB hA (by linarith) hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    slo slo shi hpositive hratio'
    (integerWindow_cell_half_scale sourceLo sourceHi S scale label (fun i => hSlength i (label i)))
    (fun j i => (integerWindow_cell_endpoint_abs (hsource (some j,i)) (hsourceLo j i) (hsourceHi j i)
      (S (some j,i)) (hSstep (some j,i)) (label (some j,i)) (hSpos (some j,i) _)).1)
    (fun j i => (integerWindow_cell_endpoint_abs (hsource (some j,i)) (hsourceLo j i) (hsourceHi j i)
      (S (some j,i)) (hSstep (some j,i)) (label (some j,i)) (hSpos (some j,i) _)).2)
    hLexp hHexp (integerBoxUniformWeights slo shi hpositive)
  apply hwindow
  intro z
  have hone : 1 ≤ Real.exp p := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp0
  exact le_mul_of_one_le_left ((integerBoxUniformWeights slo shi hpositive).nonneg z) hone

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_window_scalar_transfer (s ell : ℕ) (hell : 2 ≤ ell)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ A0 C : ℕ, 10 ≤ A0 ∧ 2 ≤ C ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p level : ℝ),
    2 ≤ p →
    let P0 := (A0 : ℝ) * (p + 1)
    let budget := (p + 2) ^ C
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → Fintype.card J = ell →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ z ∈ Fintype.piFinset (fun i => Finset.Ico (sourceLo i) (sourceHi i)), ∀ i,
      |(z i : ℝ) - (origin i : ℝ)| ≤ smoothPairCoefficientScale (H i.2) L i.1 / 2) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (ell + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  let small := min epsilon 1
  have hsmall : 0 < small := lt_min hepsilon zero_lt_one
  have hsmall1 : small ≤ 1 := min_le_right _ _
  obtain ⟨A0, hA0, heps0, hell0, hprofile0⟩ := exists_scalarInputLogFactor ell small
  obtain ⟨Cexp, hCexp, htransfer⟩ := exists_niltest_polynomial_window_transfer s ell A0 hell hA0 hsmall hsmall1
    heps0 hell0 hprofile0
  refine ⟨A0, Cexp, hA0, hCexp, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p level hp P0 budget
    hlower hlevel hnP hJ g hcomplexity D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi hLexp hHexp outer hdom
  have hsmallBound := htransfer nilmanifold p level hp hlower hlevel hnP hJ g hcomplexity
    D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi hLexp hHexp outer hdom
  have hg0 (x : I → ℤ) : 0 ≤ realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (g.eval y).re) x :=
    (realZeroExtendFinset_unit _ _ (fun y hy => (hunit y hy).2) x).1
  exact fixedParameter_scalar_tail_mono_slack outer (integerBoxUniformWeights parLo parHi hpar)
    (fun z t => realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (h y).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))
    (fun z t => realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (g.eval y).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))
    (fun _ _ => hg0 _) ((Real.exp_pos (-p)).le.trans hlower) (show small ≤ epsilon from min_le_left _ _)
    hsmallBound

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_box_scalar_transfer (s ell minimumLogFactor : ℕ) (hell : 2 ≤ ell)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ A0 C : ℕ, minimumLogFactor ≤ A0 ∧ 10 ≤ A0 ∧ 2 ≤ C ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p level : ℝ),
    2 ≤ p →
    let P0 := (A0 : ℝ) * (p + 1)
    let budget := (p + 2) ^ C
    Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → Fintype.card J = ell →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp P0 →
    ∀ (L C B A K c Cwidth : ℝ), 1 ≤ C → 0 ≤ B → 0 ≤ A → 0 ≤ K → 0 < c → 0 ≤ Cwidth →
    C ≤ Real.exp P0 → B ≤ Real.exp P0 → A ≤ Real.exp P0 → K ≤ Real.exp P0 →
    c⁻¹ ≤ Real.exp P0 → Cwidth ≤ Real.exp P0 →
    ∀ (lo : I → ℤ) (N : I → ℕ) (H : I → ℝ),
    (∀ i, H i ≤ 2 * (N i : ℝ)) → (∀ i, (N i : ℝ) ≤ A * H i) →
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ h : (I → ℤ) → ℂ,
    (∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
    ResidueSliceUpperComparison h g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (R : ℕ) (parMin : ℝ), 0 < parMin →
    (∀ j, parMin ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j, parHi j - parLo j ≤ (R : ℤ)) → (R : ℝ) ≤ Cwidth * parMin → c * L ≤ parMin →
    (∀ j, |((anchor j + (D : ℤ) * parLo j : ℤ) : ℝ) / L| ≤ C) →
    (∀ j, |((anchor j + (D : ℤ) * parHi j : ℤ) : ℝ) / L| ≤ C) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (H z.2) L z.1 ≤
      K * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ j i, |(sourceLo (some j,i) : ℝ)| ≤ B * H i / L) →
    (∀ j i, |(sourceHi (some j,i) : ℝ)| ≤ B * H i / L) →
    Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (ell + 1) ≤ H i) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  let small := min epsilon 1
  have hsmall : 0 < small := lt_min hepsilon zero_lt_one
  have hsmall1 : small ≤ 1 := min_le_right _ _
  obtain ⟨A, hA, heps0, hell0, hprofile0⟩ := exists_scalarInputLogFactor ell small
  let A0 := max minimumLogFactor A
  have hAA0 : A ≤ A0 := le_max_right _ _
  have hA0 : 10 ≤ A0 := hA.trans hAA0
  have hexpA : Real.exp (A : ℝ) ≤ Real.exp (A0 : ℝ) := Real.exp_le_exp.mpr (by exact_mod_cast hAA0)
  obtain ⟨Cexp, hCexp, htransfer⟩ := exists_niltest_polynomial_box_transfer.{u,v} s ell A0 hell hA0
    hsmall hsmall1 (heps0.trans hexpA) (hell0.trans hexpA) (hprofile0.trans hexpA)
  refine ⟨A0, 2 * Cexp, le_max_left _ _, hA0, by omega, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p level hp P0 budget
    hlower hlevel hnP hJ g hcomplexity D anchor parLo parHi hpar hD hDlog
    L C B A K c Cwidth hC hB hA hK hc hCwidth hClog hBlog hAlog hKlog hcinv hWidthlog
    lo N H hupper hratio hunit h hh hnoincrement R parMin hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright sourceLo sourceHi hsource hwinScale hsourceLo hsourceHi hLexp hHexp outer hdom
  have hp0 : 0 ≤ p := by linarith
  have hbudget : (2 * p + 2) ^ Cexp ≤ budget := scalarTransfer_doubled_budget Cexp hp
  have hlog8 : Real.exp P0 + 8 ≤ Real.exp ((A0 : ℝ) * (2 * p + 1)) :=
    scalarTransfer_doubled_log A0 hA0 hp
  have hlog : Real.exp P0 ≤ Real.exp ((A0 : ℝ) * (2 * p + 1)) := by linarith
  have hKlog' : K + 8 ≤ Real.exp ((A0 : ℝ) * (2 * p + 1)) := by linarith
  have hLpos : 0 < L := (Real.exp_pos budget).trans_le hLexp
  have hexpbudget := Real.exp_le_exp.mpr hbudget
  have hraw := htransfer nilmanifold (2 * p) level (by linarith)
    ((Real.exp_le_exp.mpr (by linarith : -(2 * p) ≤ -p)).trans hlower) hlevel
    (hnP.trans (by linarith)) hJ g (hcomplexity.mono (by linarith))
    D anchor parLo parHi hpar hD (hDlog.trans hlog) L C B A K c Cwidth hC hB hA hK hc hCwidth
    (hClog.trans hlog) (hBlog.trans hlog) (hAlog.trans hlog) hKlog' (hcinv.trans hlog) (hWidthlog.trans hlog)
    lo N H hupper hratio hunit h hh
    (hnoincrement.restrict_budget_and_error hbudget (Real.exp_le_exp.mpr (neg_le_neg hbudget)))
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    sourceLo sourceHi hsource hwinScale hsourceLo hsourceHi (hexpbudget.trans hLexp)
    (fun i => (mul_le_mul_of_nonneg_right hexpbudget (pow_nonneg hLpos.le _)).trans (hHexp i))
  have hg0 (x : I → ℤ) : 0 ≤ realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (g.eval y).re) x :=
    (realZeroExtendFinset_unit _ _ (fun y hy => (hunit y hy).2) x).1
  exact fixedParameter_scalar_tail_dominated_slack (integerBoxUniformWeights sourceLo sourceHi hsource)
    outer (integerBoxUniformWeights parLo parHi hpar)
    (fun z t => realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (h y).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))
    (fun z t => realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (g.eval y).re)
      (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))
    hp0 hdom (fun _ _ => hg0 _) ((Real.exp_pos (-p)).le.trans hlower)
    (show small ≤ epsilon from min_le_left _ _) hraw

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_niltest_scalar_transfer (s ell sourceExponent parameterExponent : ℕ) (hell : 2 ≤ ell)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I : Type u} {V : Type v} {J : Type*}
      [Fintype I] [Fintype J] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p level : ℝ),
    2 ≤ p → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p → Fintype.card J = ell →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    ∀ (lo : I → ℤ) (N : I → ℕ),
    (∀ z ∈ translatedIntegerBox lo N, (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    ∀ f : (I → ℤ) → ℝ, (∀ z ∈ translatedIntegerBox lo N, 0 ≤ f z ∧ f z ≤ 1) →
    let budget := (p + 2) ^ C
    let parameterLog := ((parameterExponent : ℝ) + 1) * p
    ResidueSliceUpperComparison (fun z => (f z : ℂ) * g.eval z) g.eval lo N budget level (Real.exp (-budget)) →
    ∀ (D : ℕ) (anchor parLo parHi : J → ℤ) (hpar : ∀ j, parLo j < parHi j),
    0 < D → (D : ℝ) ≤ Real.exp parameterLog →
    ∀ L : ℝ, Real.exp budget ≤ L → (∀ i, Real.exp budget * L ^ (ell + 1) ≤ (N i : ℝ)) →
    (∀ j, L * Real.exp (-(2 * parameterLog)) ≤ ((parHi j - parLo j : ℤ) : ℝ)) →
    (∀ j t, t ∈ Finset.Ico (parLo j) (parHi j) →
      |((anchor j + (D : ℤ) * t : ℤ) : ℝ)| ≤ Real.exp parameterLog * L) →
    ∀ (sourceLo sourceHi : Option J × I → ℤ) (hsource : ∀ z, sourceLo z < sourceHi z),
    (∀ z : Option J × I, smoothPairCoefficientScale (N z.2 : ℝ) L z.1 ≤
      Real.exp ((sourceExponent : ℝ) * p) * ((sourceHi z - sourceLo z : ℤ) : ℝ)) →
    (∀ j i x, x ∈ Finset.Ico (sourceLo (some j,i)) (sourceHi (some j,i)) →
      |(x : ℝ)| ≤ Real.exp ((sourceExponent : ℝ) * p) * ((N i : ℝ) / L)) →
    ∀ outer : FiniteProbabilityWeights (∀ i, Finset.Ico (sourceLo i) (sourceHi i)),
    (∀ z, outer.weight z ≤ Real.exp p * (integerBoxUniformWeights sourceLo sourceHi hsource).weight z) →
    outer.eventProbability (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun y => f y * (g.eval y).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun y => (g.eval y).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => (z i).val)))) ≤ Real.exp (-p) := by
  obtain ⟨A0, Cexp, hminimum, hA0, hCexp, htransfer⟩ :=
    exists_niltest_box_scalar_transfer.{u,v} s ell (sourceExponent + 5 * (parameterExponent + 1) + 6) hell hepsilon
  refine ⟨Cexp, hCexp, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p level hp hlower hlevel hnP hJ
    g hcomplexity lo N hunit f hf budget parameterLog hnoincrement D anchor parLo parHi hpar hD hDlog
    L hLexp hNexp hparWidth hparPoint sourceLo sourceHi hsource hsourceWidth hsourcePoint outer hdom
  let P0 := (A0 : ℝ) * (p + 1)
  let q := (sourceExponent : ℝ) * p
  have hp0 : 0 ≤ p := by linarith
  have hq0 : 0 ≤ q := mul_nonneg (Nat.cast_nonneg sourceExponent) hp0
  have hAr : (sourceExponent : ℝ) + 6 ≤ A0 := by
    exact_mod_cast (show sourceExponent + 6 ≤ A0 by omega)
  have hArp : 5 * ((parameterExponent : ℝ) + 1) + 6 ≤ A0 := by
    exact_mod_cast (show 5 * (parameterExponent + 1) + 6 ≤ A0 by omega)
  have hparameter : 2 ≤ parameterLog := by
    dsimp only [parameterLog]
    nlinarith [Nat.cast_nonneg (α := ℝ) parameterExponent]
  have hAten : (10 : ℝ) ≤ A0 := by exact_mod_cast hA0
  have hfive : 5 * parameterLog ≤ P0 := by
    have hm := mul_le_mul_of_nonneg_right hArp hp0
    dsimp only [parameterLog, P0]
    nlinarith
  have hqp : q + p ≤ P0 := by
    have hm := mul_le_mul_of_nonneg_right hAr hp0
    dsimp only [q, P0]
    nlinarith
  have hP0 : 0 ≤ P0 := by linarith
  have hbudget : 4 ≤ budget := calc
    4 ≤ p + 2 := by linarith
    _ = (p + 2) ^ 1 := (pow_one _).symm
    _ ≤ (p + 2) ^ Cexp := pow_le_pow_right₀ (by linarith) (by omega)
  have hexp : 4 ≤ Real.exp budget := by linarith [Real.add_one_le_exp budget]
  have hL : 1 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hscale (i : I) : 1 ≤ (N i : ℝ) / L :=
    (by linarith : 1 ≤ Real.exp budget).trans
      (affinePhysicalScales_lower hL (Real.exp_pos budget).le (by omega : 1 ≤ ell + 1) (hNexp i)).2
  obtain ⟨R, hR, hRbound, hleft, hright⟩ := scalarTransfer_parameter_geometry D hD anchor parLo parHi hpar hparameter hL hDlog hparPoint
  have hsourceEnds (j : J) (i : I) := scalarTransfer_source_endpoints
    (sourceLo (some j,i)) (sourceHi (some j,i)) (hsource (some j,i)) hp hq0 (hscale i) (hsourcePoint j i)
  let h : (I → ℤ) → ℂ := fun z => (f z : ℂ) * g.eval z
  have hreal (z : I → ℤ) : (h z).re = f z * (g.eval z).re := by
    simp only [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hh : ∀ z ∈ translatedIntegerBox lo N, 0 ≤ (h z).re ∧ (h z).re ≤ 1 := by
    intro z hz
    rw [hreal]
    exact ⟨mul_nonneg (hf z hz).1 (hunit z hz).2.1,
      (mul_le_of_le_one_left (hunit z hz).2.1 (hf z hz).2).trans (hunit z hz).2.2⟩
  have hone : 1 ≤ Real.exp P0 := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hP0
  have htwo : Real.exp (2 * parameterLog) ≤ Real.exp P0 := Real.exp_le_exp.mpr (by linarith)
  have hraw := htransfer nilmanifold p level hp hlower hlevel hnP hJ g hcomplexity
    D anchor parLo parHi hpar hD (hDlog.trans (Real.exp_le_exp.mpr (by linarith)))
    L (Real.exp (2 * parameterLog)) (Real.exp (q + p)) 1 (Real.exp q) (Real.exp (-(2 * parameterLog))) (Real.exp (5 * parameterLog))
    (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show 0 ≤ 2 * parameterLog by linarith))
    (Real.exp_pos _).le (by norm_num) (Real.exp_pos _).le (Real.exp_pos _) (Real.exp_pos _).le
    htwo (Real.exp_le_exp.mpr hqp) hone (Real.exp_le_exp.mpr (by linarith))
    (by simpa only [Real.exp_neg, inv_inv] using htwo) (Real.exp_le_exp.mpr hfive)
    lo N (fun i => (N i : ℝ)) (fun i => by nlinarith [Nat.cast_nonneg (α := ℝ) (N i)])
    (fun i => le_of_eq (one_mul (N i : ℝ)).symm) hunit h hh hnoincrement
    R (L * Real.exp (-(2 * parameterLog))) (mul_pos hLpos (Real.exp_pos _)) hparWidth hR hRbound (le_of_eq (mul_comm _ _))
    hleft hright sourceLo sourceHi hsource hsourceWidth
    (fun j i => by simpa only [mul_div_assoc] using (hsourceEnds j i).1)
    (fun j i => by simpa only [mul_div_assoc] using (hsourceEnds j i).2)
    hLexp hNexp outer hdom
  simpa only [hreal] using hraw

end Erdos3

end

end OAI
