import OAI.Combinatorics.Progressions.Geometry.AllocatedDetectedSpatialNativeSource

namespace OAI

section

namespace Erdos3

open BooleanCubeKernel VectorPolynomial
open scoped NNReal

theorem sharedWidthCanonicalSlicedSpatialChoices {G N X : Type*}
    [Fintype G] [Fintype N] [Fintype X] {q m M : ℕ} (selection : Fin q ↪ G)
    (hM : 0 < M) {p target : ℝ} (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hm : ((m + 1 : ℕ) : ℝ) ≤ p) (hq : ((q + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξle : ξ ≤ normalizedTupleNarrowWidth X N selection M p target) :
    ξ ≤ 1 ∧
    ∀ {C₀ W L Cg Centry growth earlyMesh : ℝ},
      0 ≤ C₀ → 0 ≤ W → 1 ≤ L → 0 ≤ Cg → 0 ≤ Centry →
      growth ≤ Real.exp p → W ≤ growth * L → 0 < earlyMesh →
      let δ := normalizedTupleRadius X selection M p target W
      let ρ := normalizedTupleResolution X N selection M p target C₀ W Cg Centry
      let mesh := min (δ / 4) earlyMesh
      0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧ 0 < mesh ∧
        mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
        anisotropicSpatialMeshThreshold selection N C₀ ≤ ρ ∧
        8 * probabilityProfileLipschitz ≤ ρ ∧
        2 * Fintype.card (Option (G ⊕ N)) * (2 * Centry) ≤ ρ ∧
        Fintype.card N * (2 * Centry) ≤ δ * ρ ∧
        Cg * (24 * probabilityProfileLipschitz * Fintype.card (Option (G ⊕ N) × X) / ρ) ≤
          normalizedSpatialShare target / 2 ∧
        ∀ (period : ℕ), period ≤ M ^ (m + 1) →
          allocatedTupleSpatialError (Fintype.card X) selection N M period C₀ ρ ξ W δ mesh *
            coarseReferenceMassConstant q X W L ≤ normalizedSpatialShare target / 2 := by
  obtain ⟨hξ1, hchoices⟩ :=
    sharedWidthNormalizedTupleSpatialChoices (N := N) (X := X) (m := m) selection hM hp htarget
      hm hq hG hX hMp hξ hξle
  refine ⟨hξ1, ?_⟩
  intro C₀ W L Cg Centry growth earlyMesh hC₀ hW hL hCg hCentry hgrowth hWscale hearlyMesh
    δ ρ mesh
  obtain ⟨hδ, hδ1, hmesh₀, hρ, hthreshold, hρ8, hshift, hmove, hboundary, hsite⟩ :=
    hchoices hC₀ hW hL hCg hCentry hgrowth hWscale
  have hfine : mesh ≤ δ / 4 := min_le_left _ _
  refine ⟨hδ, hδ1, hρ, lt_min hmesh₀ hearlyMesh, min_le_right _ _, hfine,
    hthreshold, hρ8, hshift, hmove, hboundary, ?_⟩
  intro period hperiod
  have hmass : 0 ≤ coarseReferenceMassConstant q X W L := by
    have hprofile := smoothProbabilityProfile_pos_zero
    unfold coarseReferenceMassConstant
    positivity
  exact (mul_le_mul_of_nonneg_right
    (allocatedTupleSpatialError_mono_mesh (Fintype.card X) selection N M period
      hC₀ hρ.le hξ.le hW hδ.le hfine) hmass).trans (hsite period hperiod)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (C V : Fin m → ℝ≥0)

theorem AllocatedSourceNumerics.shared_width_canonical_spatial_size
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau ξ Bξ : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hξ : 0 < ξ) (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (stride N : X → ℕ) (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (sharedWidthNormalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau) Bξ) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    ∀ i, 8 * (1 + W) * (stride i : ℝ) * normalizedTupleResolution X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target
      C₀ W (Real.exp Ecap) Centry ≤
        (ξ * τ) * (N i : ℝ) := by
  intro W C₀ Centry i
  obtain ⟨hW, hl₀, _, hC₀, _, _, hC₀l, _, hCentryl, hWl, hprofile⟩ :=
    hnum.late_bounds B U b S C V hR hσ
  let l := allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau
  have hl : 0 ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hQstride, hEtau]
  have hl₀l : allocatedSpatialLateLog (G := G) B P P ≤ l := by
    dsimp [l]; linarith only [hEcap, hQstride, hEtau]
  have hEcapl : Ecap ≤ l := by dsimp [l]; linarith only [hl₀, hQstride, hEtau]
  have hQstridel : Qstride ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hEtau]
  have hEtaul : Etau ≤ l := by dsimp [l]; linarith only [hl₀, hEcap, hQstride]
  exact sharedWidthNormalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n))
    (m := m) selection hp htarget hl hM hm hdim hG hX hMp
    (zero_le_one.trans hC₀) hW (Real.exp_pos _).le
    (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0)))
    (hC₀l.trans (Real.exp_le_exp.mpr hl₀l)) (hWl.trans (Real.exp_le_exp.mpr hl₀l))
    (Real.exp_le_exp.mpr hEcapl) (hCentryl.trans (Real.exp_le_exp.mpr hl₀l))
    (hprofile.trans (Real.exp_le_exp.mpr hl₀l)) (Nat.cast_nonneg _)
    ((hstride i).trans (Real.exp_le_exp.mpr hQstridel)) hτ
    (hτinv.trans (Real.exp_le_exp.mpr hEtaul)) hξ hξB (hside i)

theorem AllocatedSourceNumerics.shared_width_canonical_spatial_choices
    {P : ℝ} (hnum : AllocatedSourceNumerics B U b S C V P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    {X : Type*} [Fintype X] {dim M : ℕ} (selection : Fin dim ↪ G)
    {p target Ecap Qstride Etau earlyMesh ξ Bξ : ℝ}
    (hp : 0 ≤ p) (htarget : 0 ≤ target)
    (hEcap : 0 ≤ Ecap) (hQstride : 0 ≤ Qstride) (hEtau : 0 ≤ Etau)
    (hM : 0 < M) (hm : ((m + 1 : ℕ) : ℝ) ≤ p)
    (hdim : ((dim + 1 : ℕ) : ℝ) ≤ p)
    (hG : (Fintype.card G : ℝ) ≤ p) (hX : (Fintype.card X : ℝ) ≤ p)
    (hMp : (M : ℝ) ≤ Real.exp p)
    (hξ : 0 < ξ)
    (hξle : ξ ≤ normalizedTupleNarrowWidth X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection M p target)
    (hξB : ξ⁻¹ ≤ Real.exp Bξ)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp p)
    (hearlyMesh : 0 < earlyMesh)
    (stride N : X → ℕ) (hstridepos : ∀ i, 0 < stride i)
    (hstride : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    {τ : ℝ} (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Etau)
    (hside : ∀ i, Real.exp (sharedWidthNormalizedTupleSideLog X
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p target
      (allocatedSpatialLateLog (G := G) B P P + Ecap + Qstride + Etau) Bξ) ≤ (N i : ℝ)) :
    let W := allocatedPhysicalRootBudget B U b S (fun _ => 0)
    let C₀ := 1 + (S.value : ℝ) + W
    let Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0)
    let δ := normalizedTupleRadius X selection M p target W
    let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection M p target C₀ W (Real.exp Ecap) Centry
    let mesh := min (δ / 4) earlyMesh
    0 ≤ W ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
    W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) ∧
    0 < ξ ∧ ξ ≤ 1 ∧ 0 < δ ∧ δ ≤ 1 ∧ 0 < ρ ∧
    0 < mesh ∧ mesh ≤ earlyMesh ∧ mesh ≤ δ / 4 ∧
    (∀ i, 8 * (1 + W) * (stride i : ℝ) * ρ ≤ (ξ * τ) * (N i : ℝ)) ∧
    anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ ∧
    8 * probabilityProfileLipschitz ≤ ρ ∧
    2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) * (2 * Centry)) ≤ ρ ∧
    Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) * (2 * Centry) ≤ δ * ρ ∧
    Real.exp Ecap * (24 * probabilityProfileLipschitz *
      Fintype.card (Option (LayerSamplerVariables G I n B) × X) / ρ) ≤ normalizedSpatialShare target / 2 ∧
    (∀ period : ℕ, period ≤ M ^ (m + 1) →
      allocatedTupleSpatialError (Fintype.card X) selection
        (PrincipalTupleIndex B (layerSamplerDegree I n)) M period C₀ ρ ξ W δ mesh *
        coarseReferenceMassConstant dim X W S.value ≤ normalizedSpatialShare target / 2) ∧
    let widths := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    (∀ i, 0 < N i) ∧ (∀ z, 0 < widths z) ∧
    ∀ cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride),
      cells.Nonempty → 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z := by
  intro W C₀ Centry δ ρ mesh
  obtain ⟨hW, _, _, hC₀, hLC, hWC, _⟩ := hnum.late_bounds B U b S C V hR hσ
  have hWscale : W ≤ Fintype.card (LayerSamplerVariables G I n B) * (S.value : ℝ) := by
    simp only [W, allocatedPhysicalRootBudget, Int.cast_zero, abs_zero, Finset.sum_const_zero,
      zero_add, le_refl]
  have hL : (1 : ℝ) ≤ S.value := by exact_mod_cast S.positive
  obtain ⟨hξ1, hchoices⟩ := sharedWidthCanonicalSlicedSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hp htarget hm hdim hG hX hMp hξ hξle
  obtain ⟨hδ, hδ1, hρ, hmesh, hmeshEarly, hmeshFine, hthreshold, hρ8,
    hshift, hmove, hboundary, hsite⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := S.value) (Cg := Real.exp Ecap)
      (Centry := Centry) (growth := Fintype.card (LayerSamplerVariables G I n B))
      (zero_le_one.trans hC₀) hW hL (Real.exp_pos _).le
      (zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0)))
      hvars hWscale hearlyMesh
  have hphysical := hnum.shared_width_canonical_spatial_size B U b S C V hR hσ selection hp htarget
    hEcap hQstride hEtau hM hm hdim hG hX hMp hξ hξB stride N hstride hτ hτinv hside
  have hN (i) : 0 < N i := by
    exact_mod_cast (Real.exp_pos _).trans_le (hside i)
  have hwidth := narrowTrimmedSpatialWidths_pos (G := G)
    (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτ hξ N hN
  refine ⟨hW, hC₀, hLC, hWC, hWscale, hξ, hξ1, hδ, hδ1, hρ,
    hmesh, hmeshEarly, hmeshFine, hphysical, hthreshold, hρ8, ?_, hmove, hboundary, hsite,
    hN, hwidth, ?_⟩
  · simpa only [mul_assoc] using hshift
  · intro cells hcells
    exact (exists_selectedResidue_physical_cap (fun _ : LayerSamplerVariables G I n B => 0)
      stride hstridepos cells hcells _ hwidth (fun z => hρ8.trans
        (narrowTrimmedSpatial_residue_width_lower hW hτ hξ1 hρ.le N stride hN hstridepos
          hphysical z))).choose

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ uQ
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal
attribute [local irreducible] residueRefinedPeriod

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))
attribute [local instance 2000] fullBooleanRowSetFintype
attribute [local instance] ScalarSiteExpansion.termFinite
local notation "selectedRows" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin (s + 1))))
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable {Mk : ℕ} (hMk : 0 < Mk)
variable (selection : Fin (s + 1) ↪ G)
variable (hgood : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable (period : ℕ) [NeZero period] (stride N : Fin nX → ℕ) [∀ i, NeZero (N i)]
variable (hperiodCanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hgood m))
variable (modulus : ℕ)
variable (hmodulusRefined : modulus = residueRefinedPeriod period stride)
variable {P : ℝ} (hP : 0 ≤ P) (hMkP : (Mk : ℝ) ≤ Real.exp P)
variable (hRP : ∀ j, R j ≤ Real.exp P) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P)
variable (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
variable (hcount : ∀ j : Fin m, (Fintype.card
  (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
local notation "Tuple" => PrincipalTupleIndex (fun a : {a // ¬grid a} => B (Subtype.val a)) (fun a => degree (Subtype.val a))
local notation "jetRows" => selectedRows
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => degree (Subtype.val a))
local notation "L" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U basis S)
local notation "positiveLengths" => (fun j : Tuple => allocatedPrincipalSides_pos B U basis S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

variable (Q : Fin m → Type uQ) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
local notation "reference" => allocatedLongJetReference B U basis S jetRows
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := (Fin (s + 1))) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "embed" => (fun j : Tuple => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B (layerSamplerDegree I n)))
local notation "H" => (fun j : Tuple => H₀ (embed j))
local notation "step" => (fun j : Tuple => step₀ (embed j))
local notation "c" => (fun j : Tuple => c₀ (embed j))
local notation "hsubset" => (fun j : Tuple => hsubset₀ (embed j))
local notation "residue" => (fun j : Tuple => r₀ (embed j))
local notation "GridTuples" => PrincipalAxisTuples (α := (Fin (s + 1))) grid (allocatedPrincipalSides B U basis S)
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell grid
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
local notation "jetHaar" => Measure.pi (fun j =>
  @Measure.pi (selectedRows j) _ (fullBooleanRowSetFintype (s + 1) (Fin.val j + 1)) _
    (fun _ : selectedRows j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S

variable [CompactSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [MeasurableSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable [BorelSpace (CoefficientTorus (K := Fin (s + 1)) U)]
variable (μrows : Measure (CoefficientTorus (K := Fin (s + 1)) U))
variable [μrows.IsAddLeftInvariant] [IsProbabilityMeasure μrows]

variable [MeasurableSpace (SiteTorus (Finset (Fin (s + 1))) U)]
variable [BorelSpace (SiteTorus (Finset (Fin (s + 1))) U)]

include hb o bW hperiodCanonical hmodulusRefined μ ν μrows hR hσ hMk hgood hP hMkP hRP hRi hσi hcount in

theorem exists_allocatedCanonicalSlice_spatial_native_source_sharedWidth
    {D target Pk Prho F Qstride : ℝ}
    (hdimensions : AllocatedComparisonDimensions (G := G) B (Fin (s + 1)) selectedRows D)
    (hPk : 0 ≤ Pk)
    (hMkPk : (Mk : ℝ) ≤ Real.exp Pk)
    (hPrho : 0 ≤ Prho)
    (htarget : 0 ≤ target)
    (hF : 0 ≤ F)
    (hQstride : 0 ≤ Qstride)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hlength : Real.exp (allocatedAffineLengthLog m D P Prho Pk target F (((m + 1 : ℕ) : ℝ) * Pk + Fintype.card (Fin nX) * Qstride)) ≤ S.value)
    {δ η : ℝ}
    (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (t : ℝ)
    (htone : t ≤ 1)
    (hs : AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone)
    (hρ : 0 < ρ grid)
    (hρ1 : ρ grid ≤ 1)
    (hσsmall : ∀ j, σ j ≤ t)
    (hstep : ∀ j : Tuple, 0 < step j)
    (hδ : 0 < δ)
    (hδF : δ⁻¹ ≤ Real.exp F)
    (hdense : ∀ j : Tuple, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
    (hq : Fintype.card (Fin (s + 1)) ≤ m + 1)
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U basis S))
    (hy₀ : 0 < (wholeLaw).weight y₀)
    (T : Fin m → ℝ)
    (hT : ∀ j, partitionedIdealRadius (Fin (s + 1)) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card (Fin (s + 1)) * ((Fintype.card (Fin (s + 1)) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (T j * R j)) ≤ 1 / 4)
    (hρlog : (ρ grid : ℝ)⁻¹ ≤ Real.exp Prho)
    (hη0 : 0 ≤ η)
    (hηsmall : η ≤ Real.exp (-(target + 1 + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 4)))
    (siteRadius : ℝ≥0)
    (hrone : 1 ≤ siteRadius)
    (hsitebudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin (s + 1))) *
      (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (siteRadius : ℝ) * R j)))) ≤ 1 / 4)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0)
    (hK : ∀ j, (R j)⁻¹ ≤ K)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (siteRadius : ℝ))
    {Pbox Vlog Nlog Mlog baseAmbient : ℝ}
    (hPbox : 0 ≤ Pbox)
    (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog)
    (hMlog : 0 ≤ Mlog)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hvolume : allocatedFullGridNaturalVolume B U basis S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖((allocatedProductIdealNormalizer B U basis S rowSets : ℝ) : ℂ)⁻¹‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) *
      coefficientDeckPeriodCap selectedRows Q period ≤ Real.exp Mlog)
    (hbaseAmbient : 0 ≤ baseAmbient)
    (hvbase : Vlog ≤ baseAmbient)
    (hnbase : Nlog ≤ baseAmbient)
    (hmbase : Mlog ≤ baseAmbient)
    (hsites : (Fintype.card (Finset (Fin (s + 1))) : ℝ) ≤ baseAmbient)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ baseAmbient)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, Q j → ZMod period)) : ℝ) ≤ Real.exp baseAmbient)
    (hKbase : (K : ℝ) ≤ Real.exp baseAmbient)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp baseAmbient)
    (hpbase : (period : ℝ) ≤ Real.exp baseAmbient)
    (hrowsAmbient : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp baseAmbient)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ baseAmbient)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp baseAmbient)
    (Qgrid : ℝ≥0)
    (hQgrid : ∀ a : {a // allocatedGridAxis (I := I) U basis S.value a},
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
        (allocatedGridIntegerAxis B U basis S a).1 (allocatedGridIntegerAxis B U basis S a).2) : ℝ) + 1) ≤ Qgrid)
    {δg : ℝ}
    (hδg : 0 < δg)
    (hdenseg : ∀ tg, δg * allocatedPrincipalSides B U basis S tg ≤ (H₀ tg : ℝ))
    (Tg : ℕ)
    (hQTg : (((Fintype.card (Fin (s + 1)) + 1) * modulus : ℕ) : ℝ) / δg ≤ Tg)
    (hstepAll : ∀ tg, 0 < step₀ tg)
    (Ag : ℝ≥0)
    (hAg : LipschitzWith Ag Real.smoothTransition)
    (Pg : ℝ)
    (hPg : 1 ≤ Pg)
    (hcP : scalarCubePrimitiveEnvelope Empty Ag 16 (128 * probabilityProfileLipschitz) 1 ≤ Pg)
    (hsP : scalarCubePrimitiveEnvelope (Fin (s + 1)) Ag 1 0 modulus ≤ Pg)
    (hstrideGrid : ∀ tg, ((step₀ tg * modulus : ℕ) : ℝ) ≤ Pg)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((layerTailDegree m + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card
      ((j.val + 1) * (boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {Dg vg wg tg pg : ℝ}
    (hDg : 0 ≤ Dg)
    (hvg : 0 ≤ vg)
    (hwg : 0 ≤ wg)
    (htg : 0 ≤ tg)
    (hpg : 0 ≤ pg)
    (hcube : (Fintype.card (Fin (s + 1)) : ℝ) ≤ Dg)
    (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ Dg)
    (hrowsD : ∀ j : Fin m, ((boundedBooleanJetRows (Fin (s + 1)) (j.val + 1)).card : ℝ) ≤ Dg)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ Dg)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ Dg)
    (hRv : ∀ j, R j ≤ Real.exp vg)
    (hRiGrid : ∀ j, (R j)⁻¹ ≤ Real.exp vg)
    (hδw : δg⁻¹ ≤ Real.exp wg)
    (hTg : (Tg : ℝ) ≤ Real.exp tg)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp vg)
    (hPp₀ : Pg ≤ Real.exp pg)
    (haxesGrid : (Fintype.card {a // grid a} : ℝ) ≤ Dg)
    (hfullAxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ Dg)
    (hfullOutputs : (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1) : ℝ) ≤ Dg)
    (hambientCount : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ Dg)
    (hprofileBudget : (probabilityProfileLipschitz : ℝ) ≤ Dg)
    {Banalytic : ℝ}
    (hBanalytic : 0 ≤ Banalytic)
    (hDanalytic : Dg ≤ Banalytic)
    (hcutoffAnalytic : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Banalytic)
    (hcoordAnalytic : ((K * ∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Banalytic)
    (hgridAnalytic : (Qgrid : ℝ) ≤ Real.exp Banalytic)
    {Pnum : ℝ}
    (hPnum : 0 ≤ Pnum)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ Pnum)
    (hn : ∀ j, (n j : ℝ) ≤ Pnum)
    (hcoeffEarly : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pnum)
    (hRiEarly : ∀ j, (R j)⁻¹ ≤ Real.exp Pnum)
    (hVEarly : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Real.exp Pnum)
    {gain Pproj coarseTarget Ecoarse pGain : ℝ}
    :
    let ambientQ := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, selectedRows a.1)) (Fintype.card (Fin (s + 1)))
      (Pbox + Prho + Vlog + Nlog + Mlog + target)
    let ambientBudget := affineAmbientPrimitiveBudget baseAmbient ambientQ
    ∀ {τ Pphysical : ℝ},
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn),
    ξn ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection Mk Pphysical coarseTarget →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      (signal : ((Fin nX) → ℤ) → ℂ),
    (∀ u ∈ integerBox N, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    ∀ {lossTarget Psample Rrank Sstride εsample ηsample : ℝ},
    (∀ i, 0 < stride i) → (∀ i, 0 < N i) → (hτSpatial : 0 < τ) →
    0 ≤ Psample → (Fintype.card (Fin nX) : ℝ) ≤ Psample →
    (Fintype.card (Option (Fin (s + 1)) × (Fin nX)) : ℝ) ≤ Psample →
    0 ≤ Sstride → Sstride ≤ Real.exp Psample → 0 < εsample →
    1 / τ ≤ Real.exp Psample → 1 / εsample ≤ Real.exp Psample →
    (∀ i, (stride i : ℝ) ≤ Sstride) →
    let A := Classical.choose (exists_translated_physical_jet_l1_perturbation.{0,uJ,0} m (s + 1))
    (∀ i, Real.exp ((Psample + A) ^ A) ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp ((Psample + A) ^ A) ≤ Rrank →
    0 < ηsample → (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Psample →
    ambientBudget ≤ Psample →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Psample →
    ηsample⁻¹ ≤ Real.exp Psample →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    (hPhysicalNonneg : 0 ≤ Pphysical) → (hMkPhysicalBound : (Mk : ℝ) ≤ Real.exp Pphysical) →
    (hmPhysicalBound : ((m + 1 : ℕ) : ℝ) ≤ Pphysical) → (hCoarseNonneg : 0 ≤ coarseTarget) →
    (hDimPhysicalBound : (((s + 1) + 1 : ℕ) : ℝ) ≤ Pphysical) →
    (hGPhysicalBound : (Fintype.card G : ℝ) ≤ Pphysical) →
    (hXPhysicalBound : (Fintype.card (Fin nX) : ℝ) ≤ Pphysical) →
    lossTarget + coefficientErrorSpatialLog Pphysical + 8 ≤ target →
    ηsample ≤ Real.exp (-target) → εsample ≤ Real.exp (-target) →
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Fmodel := (m * (2 : ℝ) ^ Fintype.card (Fin (s + 1))) * (Pnum + 8) * (1 + 4 * Pnum) +
      Fintype.card (LayerSamplerAxis I n) * ((m * 2 ^ (m + 1) : ℕ) * Pk) +
      ∑ j, (Fintype.card (Q j) : ℝ) * (Fintype.card (selectedRows j) * ((m + 1 : ℕ) * Pk))
    let p := slicedGridGeometryLog Dg vg wg tg + pg
    ∀ {Pnative : ℝ}, 0 ≤ Pnative →
    Dg ∈ Set.Icc 0 Pnative → p ∈ Set.Icc 0 Pnative → vg ∈ Set.Icc 0 Pnative →
    Fmodel ∈ Set.Icc 0 Pnative → Prho ∈ Set.Icc 0 Pnative → Pk ∈ Set.Icc 0 Pnative →
    target ∈ Set.Icc 0 Pnative → Banalytic ∈ Set.Icc 0 Pnative →
    Pphysical ∈ Set.Icc 0 Pnative → Ecoarse ∈ Set.Icc 0 Pnative → pGain ∈ Set.Icc 0 Pnative →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pphysical) →
    1 / τ ≤ Real.exp Pphysical →
    Real.exp (-pGain) / 2 ≤ gain →
    pGain + 32 ≤ Pproj → pGain + 32 ≤ coarseTarget →
    pGain + 32 ≤ Ecoarse → pGain + 32 ≤ lossTarget →
    ∀ (Cproj Vproj : Fin m → ℝ≥0),
    let Acover := Classical.choose (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1))
    let coverLog := (Pproj + ((s + 1) + 2 : ℕ) + Acover) ^ Acover
    let Asample := Classical.choose (exists_allocatedCanonicalProjection_composed_budget m (s + 1) Acover)
    let Pmass := (Pproj + Asample) ^ Asample
    coverLog ≤ baseAmbient → coverLog ≤ Psample → Pmass ≤ Psample →
    (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ Cproj j * ‖z‖) →
    (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vproj j) →
    (∀ j, σ j ≤ 1) →
    (∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pmass →
    (Fintype.card (Option (Fin (s + 1)) × Fin nX) : ℝ) ≤ Pmass →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pmass) → 1 / τ ≤ Real.exp Pmass →
    let AmassWindow := Classical.choose (exists_translated_physical_jet_density_window_mass.{0,uJ,0,max uG uI uB} m (s + 1))
    (∀ i, Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ (N i : ℝ)) →
    Real.exp ((Pmass + AmassWindow) ^ AmassWindow) ≤ Rrank →
    (Fintype.card (CoefficientAmbientIndex (Fin (s + 1)) J) : ℝ) ≤ Pmass →
    ((∑ j : Fin m, (Fintype.card (BoundedCoefficientExponent (Fin (s + 1)) (j.val + 1)) : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp Pmass →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Real.exp Pphysical →
    1 ≤ Pproj → (m : ℝ) ≤ Pproj →
    (Fintype.card G : ℝ) ≤ Pproj → (S.value : ℝ) ≤ Real.exp Pproj →
    ((m + 1 : ℕ) : ℝ) * Pk ≤ Pproj →
    (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pproj → W ≤ Real.exp Pproj →
    (∀ j, (R j)⁻¹ ≤ Real.exp Pproj) → (∀ j, (σ j)⁻¹ ≤ Real.exp Pproj) →
    (∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (I j) : ℝ) ≤ Pproj) → (∀ j, (n j : ℝ) ≤ Pproj) →
    (∀ j, (Fintype.card (J j) : ℝ) ≤ Pproj) →
    (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pproj →
    (∀ j, (Cproj j : ℝ) ≤ Real.exp Pproj) → (∀ j, (Vproj j : ℝ) ≤ Real.exp Pproj) →
    (Fintype.card (Fin nX) : ℝ) ≤ Pproj →
    (Fintype.card (Option (LayerSamplerVariables G I n B) × Fin nX) : ℝ) ≤ Pproj →
    (∀ i, (stride i : ℝ) ≤ Real.exp Pproj) → τ⁻¹ ≤ Real.exp Pproj → ξn⁻¹ ≤ Real.exp Pproj →
    let Aproj := Classical.choose (Classical.choose_spec
      (exists_allocated_canonical_constructed_projection.{0,uG,uI,uB,uJ} m (s + 1)))
    (∀ i, Real.exp ((Pproj + Aproj) ^ Aproj) ≤ (N i : ℝ)) →
    Real.exp ((Pproj + Aproj) ^ Aproj) ≤ Rrank →
    ∀ {Pside : ℝ}, Pproj ≤ Pside → Pmass ≤ Pside →
    Pphysical ≤ Pside → coarseTarget ≤ Pside →
    (∀ i, Real.exp ((Pside + Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,0} m)) ^
      Classical.choose (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,0} m) + Pproj) ≤ (N i : ℝ)) →
    cells.Nonempty → ∀ (bases : Finset (Fin nX → ℤ)), bases.Nonempty →
    ∀ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z),
    gain ≤ ((wholeLaw).complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S
      (Fin nX) poly hmem N (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hW
      hτSpatial hξn stride cells hmass bases x y signal)).re →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (Pnative + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N poly u.val) * Fnative u)‖ := by
  subst modulus
  intro ambientQ ambientBudget τ Pphysical W ξn hξn hξnLe hW cells poly hp hmem signal hsignal hzero
    lossTarget Psample Rrank Sstride εsample ηsample
    hstridepos hN hτ hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    A hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP V
    hPphysical hMkPhysical hmGeometry hcoarseTarget0 hDimPhysical hGPhysical hXPhysical
    hprecision hηprecision hεprecision Amass Aanalytic Fmodel p
    Pnative hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
    Cproj Vproj Acover coverLog Asample Pmass hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hσ1 hsmall hXmass hframeMass hstrideMass hτMass
    AmassWindow hsizeMass hRrankMass hambMass hjetMass hvars
    hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj Aproj hSizeProj hRankProj
    Pside hProjSide hCapSide hpSide htargetSide hside hCells bases hbases hmass hdetected
    Cbudget Bbudget Anorm Anative Abudget budget
  have hPproj0 : 0 ≤ Pproj := zero_le_one.trans hPproj
  have hPmass : 0 ≤ Pmass := by positivity
  have hPside0 : 0 ≤ Pside := hPproj0.trans hProjSide
  have hexp := Real.exp_le_exp.mpr hProjSide
  have hnumSide : AllocatedSourceNumerics B U basis S Cproj Vproj Pside :=
    ⟨hPside0, hmProj.trans hProjSide, hKproj.trans hProjSide, hLproj.trans hexp,
      fun j => (hRproj j).trans hexp, fun j => (hσproj j).trans hexp,
      fun j => (hcountProj j).trans hProjSide, fun j => (hIproj j).trans hProjSide,
      fun j => (hnProj j).trans hProjSide, fun j => (hJproj j).trans hProjSide,
      hProfileProj.trans hexp, fun j => (hCproj j).trans hexp, fun j => (hVproj j).trans hexp,
      hWproj.trans hexp⟩
  have hperiod : period ≤ Mk ^ (m + 1) := by
    rw [hperiodCanonical]
    exact kernelPeriodCandidate_le _ _
  have hearly := (allocatedEarlyRecenteredMesh_partition_budget m (Fin nX) selection
    hPphysical hEcoarseNative.1 hGPhysical hXPhysical hMk hMkPhysical hperiod).1
  have hsideCutoff := (Classical.choose_spec (exists_allocatedCanonicalSpatial_cutoff.{uG,uI,uB,0} m)).2
    (X := Fin nX) B selection hPside0 ⟨hPphysical, hpSide⟩ ⟨hcoarseTarget0, htargetSide⟩ ⟨hPmass, hCapSide⟩
    ⟨hPproj0, hProjSide⟩ ⟨hPproj0, hProjSide⟩ (hDimPhysical.trans hpSide)
    (hKproj.trans hProjSide) (hXPhysical.trans hpSide)
  have hwidthLog : 0 ≤ normalizedTupleWidthLog
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection Pphysical coarseTarget := by
    have hQ := (anisotropicTupleEarlyBudget_bounds
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection hPphysical
      (by linarith only [hcoarseTarget0] : 0 ≤ coarseTarget + 3)).1
    have hT := spatialTupleToleranceLog_nonneg hQ
    dsimp only [normalizedTupleWidthLog]
    linarith only [hQ, hT]
  have hactualSide (i) : Real.exp (sharedWidthNormalizedTupleSideLog (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) selection Pphysical coarseTarget
      (allocatedSpatialLateLog (G := G) B Pside Pside + Pmass + Pproj + Pproj) Pproj)
      ≤ (N i : ℝ) := by
    apply (Real.exp_le_exp.mpr ?_).trans (hside i)
    refine le_trans ?_ (add_le_add hsideCutoff (le_refl Pproj))
    dsimp only [sharedWidthNormalizedTupleSideLog, normalizedTupleSideLog]
    linarith only [hwidthLog]
  obtain ⟨hW', hC₀, hLC, hWC, hWscale, hξ', hξ1, hδpos, hδ1, hρphysical, hfineMesh,
      hmeshCoarse, hmeshFine, hsizePhysical, hmeshThreshold, hρ8, hρshift, hρmove, hboundary, hsite,
      hN', hwidths, hselectedMass⟩ :=
    hnumSide.shared_width_canonical_spatial_choices B U basis S Cproj Vproj hR hσ selection
      hPphysical hcoarseTarget0 hPmass hPproj0 hPproj0 hMk hmGeometry hDimPhysical hGPhysical hXPhysical
      hMkPhysical hξn hξnLe hξProj hvars hearly stride N hstridepos hStrideProj hτ hτProj hactualSide
  have hmass' := hselectedMass cells hCells
  have hPeriodPhysical : (period : ℝ) ≤ Real.exp (Pphysical ^ 2) :=
    coefficientErrorPeriod_exp_sq hPphysical hmGeometry hMkPhysical hperiod
  have hnative := exists_allocatedCanonicalSlice_projected_native_source
    (B := B) (U := U) (basis := basis) (S := S) (hb := hb) (o := o) (bW := bW)
    (hR := hR) (hσ := hσ) (Q := Q) (ν := ν) (μ := μ) (μrows := μrows)
    (x := x) (hMk := hMk) (selection := selection) (hgood := hgood)
    (period := period) (stride := stride) (N := N) (hperiodCanonical := hperiodCanonical)
    (modulus := residueRefinedPeriod period stride) (hmodulusRefined := rfl)
    (hP := hP) (hMkP := hMkP) (hRP := hRP) (hRi := hRi) (hσi := hσi) (hcount := hcount)
    (H₀ := H₀) (step₀ := step₀) (c₀ := c₀) (hH₀ := hH₀) (hsubset₀ := hsubset₀)
    (r₀ := r₀) (hcell := hcell)
    (hdimensions := hdimensions)
    (hPk := hPk)
    (hMkPk := hMkPk)
    (hPrho := hPrho)
    (htarget := htarget)
    (hF := hF)
    (hQstride := hQstride)
    (hstride := hstride)
    (hstrideBound := hstrideBound)
    (hlength := hlength)
    (ρ := ρ)
    (t := t)
    (htone := htone)
    (hs := hs)
    (hρ := hρ)
    (hρ1 := hρ1)
    (hσsmall := hσsmall)
    (hstep := hstep)
    (hδ := hδ)
    (hδF := hδF)
    (hdense := hdense)
    (hq := hq)
    (y₀ := y₀)
    (hy₀ := hy₀)
    (T := T)
    (hT := hT)
    (hsource := hsource)
    (C := C)
    (hC := hC)
    (hchart := hchart)
    (hbudget := hbudget)
    (hρlog := hρlog)
    (hη0 := hη0)
    (hηsmall := hηsmall)
    (siteRadius := siteRadius)
    (hrone := hrone)
    (hsitebudget := hsitebudget)
    (Cforward := Cforward)
    (hforward := hforward)
    (K := K)
    (hK := hK)
    (hradius := hradius)
    (hPbox := hPbox)
    (hVlog := hVlog)
    (hNlog := hNlog)
    (hMlog := hMlog)
    (hbox := hbox)
    (hvolume := hvolume)
    (hnormalizer := hnormalizer)
    (hmask := hmask)
    (hbaseAmbient := hbaseAmbient)
    (hvbase := hvbase)
    (hnbase := hnbase)
    (hmbase := hmbase)
    (hsites := hsites)
    (haxes := haxes)
    (hlabels := hlabels)
    (hKbase := hKbase)
    (hcoords := hcoords)
    (hcutoff := hcutoff)
    (hpbase := hpbase)
    (hrowsAmbient := hrowsAmbient)
    (houtputs := houtputs)
    (hheight := hheight)
    (Qgrid := Qgrid)
    (hQgrid := hQgrid)
    (hδg := hδg)
    (hdenseg := hdenseg)
    (Tg := Tg)
    (hQTg := hQTg)
    (hstepAll := hstepAll)
    (Ag := Ag)
    (hAg := hAg)
    (Pg := Pg)
    (hPg := hPg)
    (hcP := hcP)
    (hsP := hsP)
    (hstrideGrid := hstrideGrid)
    (hBa := hBa)
    (hBi := hBi)
    (hDg := hDg)
    (hvg := hvg)
    (hwg := hwg)
    (htg := htg)
    (hpg := hpg)
    (hcube := hcube)
    (hdegree := hdegree)
    (hrowsD := hrowsD)
    (htail := htail)
    (hblocks := hblocks)
    (hRv := hRv)
    (hRiGrid := hRiGrid)
    (hδw := hδw)
    (hTg := hTg)
    (hcoeff := hcoeff)
    (hPp₀ := hPp₀)
    (haxesGrid := haxesGrid)
    (hfullAxes := hfullAxes)
    (hfullOutputs := hfullOutputs)
    (hambientCount := hambientCount)
    (hprofileBudget := hprofileBudget)
    (hBanalytic := hBanalytic)
    (hDanalytic := hDanalytic)
    (hcutoffAnalytic := hcutoffAnalytic)
    (hcoordAnalytic := hcoordAnalytic)
    (hgridAnalytic := hgridAnalytic)
    (hPnum := hPnum)
    (hI := hI)
    (hn := hn)
    (hcoeffEarly := hcoeffEarly)
    (hRiEarly := hRiEarly)
    (hVEarly := hVEarly)
    (gain := gain) (Pproj := Pproj) (coarseTarget := coarseTarget) (Ecoarse := Ecoarse) (pGain := pGain)
    (W := W) (τ := τ) (ξn := ξn)
  have hnative := hnative hW cells poly hp hmem signal hsignal hzero
    (lossTarget := lossTarget) (Pphysical := Pphysical)
    (Dphysical := (Fintype.card (LayerSamplerVariables G I n B) : ℝ))
    (Psample := Psample) (Rrank := Rrank) (Sstride := Sstride) (εsample := εsample) (ηsample := ηsample)
    hstridepos hN hτ le_rfl hPs hX hframe hSstride hSstrideP hεsample hτP hεsampleP hstrideBoundSample
    hsize hrank hRrank hηsample hamb hAmbientP hjet hηsampleP
  have hnative := hnative hwidths hmass'
    hξ1 hsizePhysical hρ8 hρshift
    hPphysical hMkPhysical hPeriodPhysical hDimPhysical hGPhysical hXPhysical hvars hWscale
    hprecision hηprecision hεprecision
    hPnative hDnative hpNative hvNative hFnative hPrhoNative hPkNative htargetNative
    hBanalyticNative hphysicalNative hEcoarseNative hpGainNative hξ' hstrideGeometry hτGeometry
    hgain hPprojGain hcoarseTarget hEcoarseGain hlossTarget
  have hnative := hnative Cproj Vproj hcoverAmbient hcoverSample hmassSample
    hCactual hVactual hσ1 hsmall hXmass hframeMass hstrideMass hτMass
    hsizeMass hRrankMass hambMass hjetMass
    hρphysical hC₀ hLC hWC hmeshThreshold hδpos.le hρmove hfineMesh
    hboundary (hsite period hperiod) hvars hWscale hmeshCoarse
    hPproj hmProj hGproj hLproj hperiodP
    hKproj hWproj hRproj hσproj hcountProj hIproj hnProj hJproj hProfileProj hCproj hVproj
    hXproj hFrameProj hStrideProj hτProj hξProj hSizeProj hRankProj hCells bases hbases hdetected
  exact hnative

end Erdos3.VectorPolynomial

end

end OAI
