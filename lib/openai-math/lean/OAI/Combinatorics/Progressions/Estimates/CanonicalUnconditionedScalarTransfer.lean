import OAI.Combinatorics.Progressions.Dynamics.ComparableScalarSelectedBudget
import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
import OAI.Combinatorics.Progressions.Geometry.ComparableScalarSliceParameterBox
import OAI.Combinatorics.Progressions.Linear.UnconditionedJointFrameDomination
import OAI.Combinatorics.Progressions.Nilpotent.NiltestScalarTransfer

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_joint_scalar_transfer (s : ℕ) :
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
    ∀ (origin sourceLo sourceHi : Option J × I → ℤ) (_hsource : ∀ z, sourceLo z < sourceHi z),
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
    ∀ (bases : Finset (I → ℤ)) (hbases : bases.Nonempty)
      (width : Option J × I → ℝ) (hwidth : ∀ z, 0 < width z)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    (∀ z : J × I, 8 * (probabilityProfileLipschitz : ℝ) ≤ width (some z.1,z.2)) →
    ∀ _hframe : ∀ z : bases × rectangularWeightIndices 0 width 1, ∀ t,
      jointIntegerFrame (z.1.val,z.2.val) t.1 t.2 ∈ Finset.Ico (sourceLo t) (sourceHi t),
    ((∏ t, ((sourceHi t - sourceLo t : ℤ) : ℝ)) *
      ((bases.card : ℝ)⁻¹ * ∏ t : J × I, 2 / width (some t.1,t.2))) ≤ Real.exp p →
    (selectedJointReference bases hbases (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_niltest_threshold_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hLexp hHexp
    bases hbases width hwidth hZ hscale hframe hframeBudget
  let reference := selectedJointReference bases hbases (fun _ : I => 1) {0} width hwidth hZ
  let frame := selectedJointFrameBoxMap bases width sourceLo sourceHi hframe
  have hdom := selectedJointReference_frame_box_domination bases hbases width hwidth hZ hscale
    sourceLo sourceHi hsource hframe hframeBudget
  have htail := htransfer nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    hbudget hLexp hHexp (reference.fiberLaw frame) hdom
  dsimp only [reference, frame] at htail
  rw [selectedJointReference_frame_box_eventProbability] at htail
  exact htail

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_trimmed_scalar_transfer (s : ℕ) :
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
    (selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_unconditioned_joint_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim sourceLo sourceHi origin
    hwinScale hW hsourceLo hsourceHi
    m n d Z G U pref common b cellLog meshLog hbudget hLexp hHexp
  have hN (i : I) : 0 < N i := by have := hmargin i; omega
  have hsource : ∀ z, sourceLo z < sourceHi z :=
    jointFrameSource_nonempty N hN width (fun z => (hwidth z).le)
  have hframe := jointIntegerFrame_mem_sourceBox N margin (fun i => (hmargin i).le) width hroot
  have hwidthOne (z : J × I) : (1 : ℝ) ≤ width (some z.1,z.2) := by
    have hprofileOne : (1 : ℝ) ≤ (probabilityProfileLipschitz : ℝ) := by
      exact_mod_cast probabilityProfileLipschitz_one_le
    have hz := hscale z
    linarith
  have hframeBudget := jointFrameSource_volume_cap_le_exp N margin hmargin hloss width hwidthOne hpDim
  exact htransfer nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    origin sourceLo sourceHi hsource hwinScale hW hsourceLo hsourceHi
    hbudget hLexp hHexp (trimmedIntegerBox N margin) (trimmedIntegerBox_nonempty N margin hmargin)
    width hwidth hZ hscale hframe hframeBudget

end Erdos3

end

section

namespace Erdos3

open BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

universe u v

theorem exists_unconditioned_trimmed_threshold_transfer (s : ℕ) :
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
    (selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
      (fun z => Real.exp (-p) <
      (integerBoxUniformWeights parLo parHi hpar).mean (fun t =>
        realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (h z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
        (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox lo N) (fun z => (g.eval z).re)
          (smoothAffineSample (fun j => anchor j + (D : ℤ) * (t j).val) (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, htransfer⟩ := exists_unconditioned_trimmed_scalar_transfer.{u,v} s
  refine ⟨E, hE, ?_⟩
  intro I V J _ _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim sourceLo sourceHi origin
    hwinScale hW hsourceLo hsourceHi
    hbudget hLexp hHexp
  exact htransfer nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htarget hepsInv hlower hlevel hnP hJ hJlog hprofile g hcomplexity
    k0 D anchor parLo parHi hpar hD hDlog L C B A K c Cwidth hC hB hA hK hc hCwidth
    hClog hBlog hAlog hKlog hcinv hWidthlog lo N H hupper hratio hunit h hh hnoincrement
    R parMin hparMin hparSide hparWidth hwidthRatio hrelative hleft hright
    width hwidth hZ margin hmargin hloss hroot hscale hpDim
    origin hwinScale hW hsourceLo hsourceHi hbudget hLexp hHexp

end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance canonicalScalarTailFinDecidableEq (n : ℕ) : DecidableEq (Fin n) :=
  Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox

theorem exists_canonicalScalarTailApplication (s d : ℕ) (hd : 2 ≤ d) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    (d : ℝ) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant d τ ≤ Real.exp P0 →
    4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ 2 * L) →
    ∀ (N : I → ℕ),
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∀ (data : CanonicalScalarGeometryData d L Wsite τ parameters N),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin data.hmargin) (fun _ : I => 1) {0}
          width data.hwidth data.hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) data.hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  let E := Classical.choose (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)
  have hE : 2 ≤ E := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)).1
  refine ⟨E, hE, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hdP0 hprofile
    hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget g hg L parameters hlo hhi
    N hunit Wsite width margin data
  have hτ := data.hτ
  have hτ1 := data.hτ1
  have hbox := data.parameterBox
  have hparam := data.hparam
  have hLpos := hbox.2.1
  have hparSide := hbox.2.2.1
  have hparRadius := hbox.2.2.2.1
  have hrad := hbox.2.2.2.2.1
  have hrelative := hbox.2.2.2.2.2.1
  have hleft := hbox.2.2.2.2.2.2.1
  have hright := hbox.2.2.2.2.2.2.2.1
  have hwidth := data.hwidth
  have hmargin := data.hmargin
  have hZ := data.hZ
  intro h hh hupper
  as_aux_lemma =>
    have hboxGeometry := data.sourceGeometry
    have hroot := data.hroot
    have hloss := data.hloss
    have hscale := data.hscale
    have hPone : (1 : ℝ) ≤ Real.exp P0 := Real.one_le_exp_iff.mpr hP0
    have hPthree : (3 : ℝ) ≤ Real.exp P0 := by linarith only [htargetP0, hp, Real.add_one_le_exp P0]
    have htwoP0 : (2 : ℝ) ≤ Real.exp P0 := (by norm_num : (2 : ℝ) ≤ 3).trans hPthree
    have hK0 : 0 ≤ canonicalJointFrameWindowConstant d τ :=
      (by norm_num : (0 : ℝ) ≤ 2).trans (canonicalJointFrameWindowConstant_two_le d hτ hτ1)
    have htail := (Classical.choose_spec
      (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)).2 nilmanifold p epsilon P0 level budget hp hepsilon hepsilon1 hP0
      htargetP0 hepsP0 hlevel hlevel2
      hnTarget (by simpa using hd) (by simpa only [Fintype.card_fin] using hdP0) hprofile
      g hg (⟨0, by omega⟩ : Fin d) 1 0 0 (fun j => (parameters j : ℤ)) hparam
      (by decide) (by simpa using hPone)
      L 2 1 1 (canonicalJointFrameWindowConstant d τ) 1 3
      (by norm_num) (by norm_num) (by norm_num) hK0 (by norm_num) (by norm_num)
      htwoP0 hPone hPone hKP0 (by simpa using hPone) hPthree
      0 N (fun i => 2 * (N i : ℝ)) (fun _ => le_rfl)
      (fun i => by nlinarith only [Nat.cast_nonneg (α := ℝ) (N i)]) hunit h hh hupper
      (canonicalScalarParameterRadius L) L hLpos hparSide hparRadius hrad hrelative
      (fun _ => by simpa only [Pi.zero_apply, mul_zero, add_zero, Int.cast_zero] using hleft)
      (fun j => by simpa using hright j)
      width hwidth hZ margin hmargin hloss hroot
      (fun z => by simpa only [residueProfileWidth, Nat.cast_one, div_one] using hscale (some z.1,z.2))
      hframeDim 0 hboxGeometry.1 (by simpa only [Fintype.mem_piFinset, Pi.zero_apply, width, Wsite, τ, L] using hboxGeometry.2.1)
      (fun j i => by simpa only [one_mul] using hboxGeometry.2.2.1 j i)
      (fun j i => by simpa only [one_mul] using hboxGeometry.2.2.2 j i)
      (by simpa only [Fintype.card_fin] using hbudget) le_rfl
      (by simpa only [Fintype.card_fin] using data.physicalSize)
    simp only [Pi.zero_apply, zero_add, Nat.cast_one, one_mul] at htail
    exact htail

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance comparableScalarSliceFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox

theorem exists_comparableScalarSliceGeometryTransfer (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ density : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    ((r*d : ℕ) : ℝ) ≤ Real.exp P0 → 2 * (r : ℝ) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < density → (density / 2)⁻¹ ≤ Real.exp P0 →
    4 * (r : ℝ) / density ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant (r*d) τ ≤ Real.exp P0 →
    4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ (q : ℕ) (S : ResidueBoxSlice parameters q),
      0 < q → (q : ℝ) ≤ Real.exp P0 → 4 ≤ density * L →
      (∀ j, density * L / 2 ≤ (S.length j : ℝ)) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((((r*d : ℕ) : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < S.length j),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (S.length j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (S.start j : ℤ) + (q : ℤ) * (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  let E := Classical.choose (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)
  have hE : 2 ≤ E := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)).1
  refine ⟨E, hE, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ density
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hDP0 hratioP0 hprofile
    hdensity hdensityP0 hwidthP0 hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget
    g hg L parameters hlo hhi q S hq hqP0 hlong hlength N hN hunit Wsite width margin
  have data := comparableScalarGeometryData d r hd hr hP0 hbudget0 hDP0 hprofile hσ hσ1 hτP0
    parameters hlo hhi N hN
  have hratio : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
  obtain ⟨hparam, hparMin, hparSide, hparWidth, hwidthRatio, hrelative, hleft, hright⟩ :=
    S.comparableScalarSliceParameterBox_bounds hq data.hL hdensity hratio hlong hhi hlength
  refine ⟨data.hwidth, data.hmargin, data.hZ, hparam, ?_⟩
  intro h hh hupper
  have hPone : (1 : ℝ) ≤ Real.exp P0 := Real.one_le_exp_iff.mpr hP0
  have hdD : d ≤ r*d := by have hh := Nat.mul_le_mul_right d hr; omega
  have hdP0 : (d : ℝ) ≤ Real.exp P0 :=
    (show (d : ℝ) ≤ ((r*d : ℕ) : ℝ) by exact_mod_cast hdD).trans hDP0
  have hK0 : 0 ≤ canonicalJointFrameWindowConstant (r*d) τ :=
    (by norm_num : (0 : ℝ) ≤ 2).trans
      (canonicalJointFrameWindowConstant_two_le (r*d) data.hτ data.hτ1)
  have htail := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)).2 nilmanifold p epsilon P0 level budget
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2
    hnTarget (by simpa using hd) (by simpa only [Fintype.card_fin] using hdP0) hprofile
    g hg (⟨0, by omega⟩ : Fin d) q (fun j => (S.start j : ℤ)) 0
    (fun j => (S.length j : ℤ)) hparam hq hqP0
    L (2 * (r : ℝ)) 1 1 (canonicalJointFrameWindowConstant (r*d) τ)
    (density / 2) (4 * (r : ℝ) / density)
    (by linarith) (by norm_num) (by norm_num) hK0 (by positivity) (by positivity)
    hratioP0 hPone hPone hKP0 hdensityP0 hwidthP0
    0 N (fun i => 2 * (N i : ℝ)) (fun _ => le_rfl)
    (fun i => by nlinarith only [Nat.cast_nonneg (α := ℝ) (N i)]) hunit h hh hupper
    ⌈(r : ℝ) * L⌉₊ (density * L / 2) hparMin hparSide hparWidth hwidthRatio hrelative
    hleft hright width data.hwidth data.hZ margin data.hmargin data.hloss data.hroot
    (fun z => by simpa only [residueProfileWidth, Nat.cast_one, div_one]
      using data.hscale (some z.1,z.2)) hframeDim 0
    data.sourceGeometry.1
    (by simpa only [Fintype.mem_piFinset, Pi.zero_apply, width, Wsite, τ, L]
      using data.sourceGeometry.2.1)
    (fun j i => by simpa only [one_mul] using data.sourceGeometry.2.2.1 j i)
    (fun j i => by simpa only [one_mul] using data.sourceGeometry.2.2.2 j i)
    (by simpa only [Fintype.card_fin] using hbudget) le_rfl
    (by simpa only [Fintype.card_fin] using data.physicalSize)
  exact htail

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance classicalFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _
attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox

theorem exists_comparableScalarTailApplication (s d r : ℕ) (hd : 2 ≤ d) (hr : 2 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    ((r*d : ℕ) : ℝ) ≤ Real.exp P0 → ((r : ℝ) + 1) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant (r*d) τ ≤ Real.exp P0 →
    4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ (N : I → ℕ),
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∀ (data : ComparableScalarGeometryData d r L Wsite τ parameters N),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin data.hmargin) (fun _ : I => 1) {0}
          width data.hwidth data.hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) data.hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  let E := Classical.choose (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)
  have hE : 2 ≤ E := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)).1
  refine ⟨E, hE, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hDP0 hrPlusOneP0 hprofile
    hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget g hg L parameters hlo hhi
    N hunit Wsite width margin data
  have hτ := data.hτ
  have hτ1 := data.hτ1
  have hbox := data.parameterBox
  have hparam := data.hparam
  have hLpos := hbox.2.1
  have hparSide := hbox.2.2.1
  have hparRadius := hbox.2.2.2.1
  have hrad := hbox.2.2.2.2.1
  have hrelative := hbox.2.2.2.2.2.1
  have hleft := hbox.2.2.2.2.2.2.1
  have hright := hbox.2.2.2.2.2.2.2.1
  have hwidth := data.hwidth
  have hmargin := data.hmargin
  have hZ := data.hZ
  intro h hh hupper
  have hboxGeometry := data.sourceGeometry
  have hroot := data.hroot
  have hloss := data.hloss
  have hscale := data.hscale
  have hPone : (1 : ℝ) ≤ Real.exp P0 := Real.one_le_exp_iff.mpr hP0
  have hdD : d ≤ r*d := by have hh := Nat.mul_le_mul_right d hr; omega
  have hdP0 : (d : ℝ) ≤ Real.exp P0 := (show (d : ℝ) ≤ ((r*d : ℕ) : ℝ) by exact_mod_cast hdD).trans hDP0
  have hrP0 : (r : ℝ) ≤ Real.exp P0 := (le_add_of_nonneg_right zero_le_one).trans hrPlusOneP0
  have hPthree : (3 : ℝ) ≤ Real.exp P0 := by linarith only [htargetP0, hp, Real.add_one_le_exp P0]
  have htwoP0 : (2 : ℝ) ≤ Real.exp P0 := (by norm_num : (2 : ℝ) ≤ 3).trans hPthree
  have hK0 : 0 ≤ canonicalJointFrameWindowConstant (r*d) τ :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (canonicalJointFrameWindowConstant_two_le (r*d) hτ hτ1)
  have htail := (Classical.choose_spec
    (exists_unconditioned_trimmed_threshold_transfer.{u,v} s)).2 nilmanifold p epsilon P0 level budget hp hepsilon hepsilon1 hP0
    htargetP0 hepsP0 hlevel hlevel2
    hnTarget (by simpa using hd) (by simpa only [Fintype.card_fin] using hdP0) hprofile
    g hg (⟨0, by omega⟩ : Fin d) 1 0 0 (fun j => (parameters j : ℤ)) hparam
    (by decide) (by simpa using hPone)
    L (r : ℝ) 1 1 (canonicalJointFrameWindowConstant (r*d) τ) 1 ((r : ℝ)+1)
    (by exact_mod_cast (show 1 ≤ r by omega)) (by norm_num) (by norm_num) hK0 (by norm_num) (by positivity)
    hrP0 hPone hPone hKP0 (by simpa using hPone) hrPlusOneP0
    0 N (fun i => 2 * (N i : ℝ)) (fun _ => le_rfl)
    (fun i => by nlinarith only [Nat.cast_nonneg (α := ℝ) (N i)]) hunit h hh hupper
    (comparableScalarParameterRadius (r : ℝ) L) L hLpos hparSide hparRadius hrad hrelative
    (fun _ => by simpa only [Pi.zero_apply, mul_zero, add_zero, Int.cast_zero] using hleft)
    (fun j => by simpa using hright j)
    width hwidth hZ margin hmargin hloss hroot
    (fun z => by simpa only [residueProfileWidth, Nat.cast_one, div_one] using hscale (some z.1,z.2))
    hframeDim 0 hboxGeometry.1 (by simpa only [Fintype.mem_piFinset, Pi.zero_apply, width, Wsite, τ, L] using hboxGeometry.2.1)
    (fun j i => by simpa only [one_mul] using hboxGeometry.2.2.1 j i)
    (fun j i => by simpa only [one_mul] using hboxGeometry.2.2.2 j i)
    (by simpa only [Fintype.card_fin] using hbudget) le_rfl
    (by simpa only [Fintype.card_fin] using data.physicalSize)
  simp only [Pi.zero_apply, zero_add, Nat.cast_one, one_mul] at htail
  exact htail

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section
local instance canonicalScalarGeometryTransferFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

theorem exists_canonicalScalarGeometryTransfer (s d : ℕ) (hd : 2 ≤ d) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      (p epsilon P0 level budget σ : ℝ),
    2 ≤ p → 0 < epsilon → epsilon ≤ 1 → 0 ≤ P0 → 3 * p + 10 ≤ P0 →
    epsilon⁻¹ ≤ Real.exp P0 → Real.exp (-p) ≤ level → level ≤ 2 →
    (Fintype.card I : ℝ) ≤ p →
    (d : ℝ) ≤ Real.exp P0 → (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 →
    0 < σ → σ ≤ 1 →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    τ⁻¹ ≤ Real.exp P0 → canonicalJointFrameWindowConstant d τ ≤ Real.exp P0 →
    4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ p →
    0 ≤ budget →
    scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon p P0 ≤ budget →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ 2 * L) →
    ∀ (N : I → ℕ), (∀ i, Real.exp (((d : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < parameters j),
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-p) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-p) := by
  obtain ⟨E, hE, happly⟩ := exists_canonicalScalarTailApplication.{u,v} s d hd
  refine ⟨E, hE, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p epsilon P0 level budget σ
    hp hepsilon hepsilon1 hP0 htargetP0 hepsP0 hlevel hlevel2 hnTarget hdP0 hprofile
    hσ hσ1 τ hτP0 hKP0 hframeDim hbudget0 hbudget g hg L parameters hlo hhi
    N hN hunit Wsite width margin
  have data := canonicalScalarGeometryData d hd hP0 hbudget0 hdP0 hprofile hσ hσ1 hτP0
    parameters hlo hhi N hN
  refine ⟨data.hwidth, data.hmargin, data.hZ, data.hparam, ?_⟩
  exact happly nilmanifold p epsilon P0 level budget σ hp hepsilon hepsilon1 hP0
    htargetP0 hepsP0 hlevel hlevel2 hnTarget hdP0 hprofile hσ hσ1 hτP0 hKP0
    hframeDim hbudget0 hbudget g hg parameters hlo hhi N hunit data

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v
noncomputable section

local instance canonicalUnconditionedScalarFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card

def CanonicalUnconditionedScalarTransferStatement (s d : ℕ) (epsilon : ℝ) : Prop :=
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d0 : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d0)
      {p σ level : ℝ}, 2 ≤ p → (Fintype.card I : ℝ) ≤ p →
      0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp p → Real.exp (-p) ≤ level → level ≤ 2 →
    ∀ g : nilmanifold.Niltest (fun _ : I => 1), g.ComplexityLE p →
    let target := 8 * ((d : ℝ) + 1) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : Fin d → ℕ),
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ 2 * L) →
    ∀ (N : I → ℕ), (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N,
        (g.eval z).im = 0 ∧ 0 ≤ (g.eval z).re ∧ (g.eval z).re ≤ 1) →
    let τ := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := Fin d) Wsite τ N
    let margin := spatialTrimMargin τ N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z)
      (hparam : ∀ j : Fin d, (0 : ℤ) < parameters j),
    budget ≤ (p + F) ^ F ∧
    ∀ h : (I → ℤ) → ℂ,
      (∀ z ∈ translatedIntegerBox (0 : I → ℤ) N, 0 ≤ (h z).re ∧ (h z).re ≤ 1) →
      ResidueSliceUpperComparison h g.eval 0 N budget level (Real.exp (-budget)) →
      (selectedJointReference (trimmedIntegerBox N margin)
        (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ).eventProbability
        (fun z => Real.exp (-target) <
          (integerBoxUniformWeights (fun _ : Fin d => (0 : ℤ)) (fun j => (parameters j : ℤ)) hparam).mean
            (fun t => realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N) (fun x => (h x).re)
              (smoothAffineSample (fun j => (t j).val)
                (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) -
              (1 + epsilon) * level * realZeroExtendFinset (translatedIntegerBox (0 : I → ℤ) N)
                (fun x => (g.eval x).re)
                (smoothAffineSample (fun j => (t j).val)
                  (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)))) ≤ Real.exp (-target)

theorem exists_canonical_unconditioned_scalar_transfer (s d : ℕ) (hd : 2 ≤ d)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    CanonicalUnconditionedScalarTransferStatement.{u,v} s d epsilon := by
  unfold CanonicalUnconditionedScalarTransferStatement
  obtain ⟨E, hE, hgeom⟩ := exists_canonicalScalarGeometryTransfer.{u,v} s d hd
  obtain ⟨A, C, F, hA, hC, hF, hselect⟩ :=
    exists_canonicalScalarSelectedBudget E d hE hepsilon hepsilon1
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro I V _ _ _ _ _ _ _ d0 nilmanifold p σ level hp hn hσ hσ1 hσinv hlevel hlevel2
    g hg target budget L parameters hlo hhi N hN hunit τ Wsite width margin
  let P0 := (A : ℝ) * (target + 1)
  obtain ⟨hpTarget, htarget, hnTarget, hframeDim, hP0, htargetP0,
    hepsP0, hprofile, hdP0, htwoP0, hτP0, hKP0, hbudget0, hthreshold,
    hNlog, hbudgetFinal⟩ := hselect (Fintype.card I) hp hn hσ hσinv
  have hframeDim' : 4 * ((Fintype.card (Fin d × I) : ℝ) + 1) ≤ target := by
    simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using hframeDim
  have hthreshold' : scalarInitialThreshold E (Fintype.card (Option (Fin d) × I))
      (Fintype.card I) d epsilon target P0 ≤ budget := by
    have hc : Fintype.card (Option (Fin d) × I) = (d + 1) * Fintype.card I := by simp
    rw [hc]
    exact hthreshold
  have hNphysical (i) : Real.exp (((d : ℝ) + 4) * (budget + P0 + 20)) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hNlog).trans (hN i)
  obtain ⟨hwidth, hmargin, hZ, hparam, htail⟩ :=
    hgeom (I := I) (V := V) nilmanifold target epsilon P0 level budget σ htarget hepsilon hepsilon1
      hP0 htargetP0 hepsP0 ((Real.exp_le_exp.mpr (neg_le_neg hpTarget)).trans hlevel)
      hlevel2 hnTarget hdP0 hprofile hσ hσ1 hτP0 hKP0 hframeDim' hbudget0 hthreshold'
      g (hg.mono hpTarget) parameters hlo hhi N hNphysical hunit
  exact ⟨hwidth, hmargin, hZ, hparam, hbudgetFinal, htail⟩

end
end Erdos3

end

end OAI
