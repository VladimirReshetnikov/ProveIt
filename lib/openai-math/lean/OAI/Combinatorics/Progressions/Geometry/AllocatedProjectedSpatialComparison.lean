import OAI.Combinatorics.Progressions.Dynamics.SharedWidthNormalizedTupleSideBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedProjectedNormalizedComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]

noncomputable def allocatedSpatialLateLog (P Q : ℝ) : ℝ :=
  2 * Q + 3 + Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) * allocatedAmbientLog m P

theorem allocatedSpatialLateInputBounds
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (C V : Fin m → ℝ≥0) {P Q W : ℝ} (hP : 0 ≤ P) (hPQ : P ≤ Q)
    (hm : (m : ℝ) ≤ P) (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P) (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P)
    (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P) (hW : 0 ≤ W) (hWQ : W ≤ Real.exp Q) :
    let l := allocatedSpatialLateLog (G := G) B P Q
    let C₀ := 1 + (S.value : ℝ) + W
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    0 ≤ l ∧ Q ≤ l ∧ 1 ≤ C₀ ∧ (S.value : ℝ) ≤ C₀ ∧ W ≤ C₀ ∧
      C₀ ≤ Real.exp l ∧ cap ≤ Real.exp l ∧
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l ∧
      W ≤ Real.exp l ∧ (probabilityProfileLipschitz : ℝ) ≤ Real.exp l := by
  intro l C₀ cap
  have hQ : 0 ≤ Q := hP.trans hPQ
  let caplog := (Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) : ℝ) * allocatedAmbientLog m P
  have hcaplog : 0 ≤ caplog := mul_nonneg (Nat.cast_nonneg _) (allocatedAmbientLog_nonneg m hP)
  have hleq : l = 2 * Q + 3 + caplog := rfl
  have hl : 0 ≤ l := by rw [hleq]; positivity
  have hQl : Q ≤ l := by linarith
  have hLQ := hLP.trans (Real.exp_le_exp.mpr hPQ)
  have hcapbase := (allocatedAmbientConstants_exp_bounds B R σ S.value S.positive
    (fun j => Fintype.card (J j)) C V hP hm hR hσ hRP hσP hcount hI hn hJ hAP hLP hCP hVP).1
  have hcap : cap ≤ Real.exp l := by
    calc
      _ ≤ (Real.exp (allocatedAmbientLog m P)) ^ Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m) := by
        dsimp [cap]
        gcongr
      _ = Real.exp caplog := by rw [← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hC : C₀ ≤ Real.exp l := by
    have h1 : 1 ≤ Real.exp Q := Real.one_le_exp hQ
    calc
      _ ≤ 3 * Real.exp Q := by dsimp [C₀]; linarith
      _ ≤ Real.exp 2 * Real.exp Q := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) (Real.exp_pos _).le
      _ = Real.exp (Q + 2) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hvsucc : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1 ≤ Real.exp Q := by
    linarith [Real.add_one_le_exp Q]
  have hentryeq : allocatedPhysicalEntryBudget B U b S (fun _ => 0) =
      1 + ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * S.value := by
    simp [allocatedPhysicalEntryBudget, allocatedPhysicalRootBudget]
    ring
  have hentry : allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ Real.exp l := by
    rw [hentryeq]
    calc
      _ ≤ 1 + Real.exp Q * Real.exp Q := add_le_add le_rfl
        (mul_le_mul hvsucc hLQ (Nat.cast_nonneg _) (Real.exp_pos _).le)
      _ = 1 + Real.exp (2 * Q) := by rw [← Real.exp_add, ← two_mul]
      _ ≤ Real.exp (2 * Q + 1) := one_add_le_exp_succ (by positivity) le_rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  refine ⟨hl, hQl, ?_, ?_, ?_, hC, hcap, hentry,
    hWQ.trans (Real.exp_le_exp.mpr hQl), hAP.trans (Real.exp_le_exp.mpr (hPQ.trans hQl))⟩
  all_goals dsimp [C₀]; linarith [Nat.cast_nonneg (α := ℝ) S.value]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedSpatiallyNormalizedTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
    ∃ A Amass : ℕ, 2 ≤ A ∧ 2 ≤ Amass ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    {P : ℝ} (_hP : 0 ≤ P) (_hG : (Fintype.card G : ℝ) ≤ P)
    (_hL : (S.value : ℝ) ≤ Real.exp P)
    {M : ℕ} (hM : 0 < M) (selection : Fin dim ↪ G)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x) (_hdim : dim ≤ m + 1),
    ∃ (d : ℕ) (hd : 0 < d), let : NeZero d := ⟨hd.ne'⟩
    (d : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin dim)) U)] [BorelSpace (SiteTorus (Finset (Fin dim)) U)]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B (Fin dim) Cinv 1 j)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let O := fun j : Fin m => BoundedBooleanJet (Fin dim) (j.val + 1)
    let rows := fun j => (Subtype.val : O j → Finset (Fin dim))
    let density := allocatedCoefficientDensity B U b hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let cover := quotientIntegerCover (coefficientIntegerLattice U) d
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin dim) (j.val + 1) => ν j))
    ∃ g : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S) →
        EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin dim) (j.val + 1)) → ℝ,
      (∀ y, Continuous (g y)) ∧ (∀ y z, g y z ∈ Set.Icc (0 : ℝ) cap) ∧
      (∀ y, Integrable (g y) ξ) ∧ (∀ y, (∫ z, g y z ∂ξ) = 1) ∧
      (∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
        (euclideanCoefficientJetMap U (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y)
          (fun j => (Subtype.val : BoundedBooleanJet (Fin dim) (j.val + 1) → Finset (Fin dim)))) =
            realDensityMeasure ξ (g y)) ∧
      ((if keepProjection then And
        (∀ y, physicalDensityProjection.{_, _, uX, 0} U
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) d density (g y))
      else id) <|
      ∀ (_hm : (m : ℝ) ≤ P)
        (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
        (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_hcount : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
        (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
        (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
        (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
        (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
        {X : Type uX} [Fintype X] [DecidableEq X]
        {p Etarget : ℝ} (_hp : 0 ≤ p) (_hEtarget : 0 ≤ Etarget)
        (_hvarsp : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
        (_hIp : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (_hnp : ∀ j, (n j : ℝ) ≤ p)
        (_hJp : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
        (_hXp : (Fintype.card X : ℝ) ≤ p) (_hCp : ∀ j, (C j : ℝ) ≤ Real.exp p)
        (_hMp : (M : ℝ) ≤ Real.exp p)
        (_hmsp : ((m + 2 : ℕ) : ℝ) ≤ p),
        let ξ₀ := normalizedTupleNarrowWidth X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        let hξ := normalizedTupleNarrowWidth_pos X (PrincipalTupleIndex B (layerSamplerDegree I n))
          selection M p Etarget
        ∀ {D : ℝ} (_hD : D ≤ Real.exp p)
        {Perr Pmass : ℝ} (_hPerr : P ≤ Perr)
        (_hAccuracy : allocatedCoefficientAccuracyLog m p (Etarget + 3) ≤ Perr)
        (_hQ : allocatedScalarSamplingBudget m dim A P Perr ≤ Pmass)
        (_hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmass)
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ),
        let l := allocatedSpatialLateLog (G := G) B P Pmass
        let δ := normalizedTupleRadius X selection M p Etarget W
        let mesh := δ / 4
        ∀ (_hWScale : W ≤ D * S.value) (_hWP : W ≤ Real.exp Pmass)
        (_hξP : ξ₀⁻¹ ≤ Real.exp Pmass)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((Pmass + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((Pmass + Amass) ^ Amass) ≤ Rrank)
        (_hspatialSize : ∀ t, Real.exp (normalizedTupleSideLog X
          (PrincipalTupleIndex B (layerSamplerDegree I n)) selection p Etarget l) ≤ (N t : ℝ))
        (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
        (base : X → ℤ)
        (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
        (_hcells : cells.Nonempty) (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
        (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        {Pc T : ℝ} (_hPc : 0 ≤ Pc) (_hPcErr : Pc ≤ Perr) (_hT : 0 ≤ T)
        (_hMP : (M : ℝ) ≤ Real.exp Pc) (_hRupper : ∀ j, R j ≤ Real.exp Pc)
        (_hRi : ∀ j, (R j)⁻¹ ≤ Real.exp Pc) (_hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp Pc)
        (_hcountc : ∀ j : Fin m,
          (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp Pc)
        (_hstridec : ∀ t, (stride t : ℝ) ≤ Real.exp T)
        (_hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B (Fin dim) O Pc
          (allocatedCoefficientAccuracyLog m p (Etarget + 3))
          ((m+1 : ℕ)*Pc + Fintype.card X*T)) ≤ S.value),
        let widths := narrowTrimmedSpatialWidths (G := G)
          (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ₀ N
        let baseDensity := fun (a : X → ℤ) z => density (affineSampleCoefficientTorus U
          (fun j => translate (fun t => (a t : ℝ)) (poly j))
          (fun j => coefficients_translate_mem (U j) (fun t => (a t : ℝ)) (poly j) (hmem j))
          (fun k t => (z (k, t) : ℝ)))
        let Z := selectedJointDensityMass bases stride cells widths baseDensity
        ∃ (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z),
        (|Z - 1| ≤ Real.exp (-Pmass) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
          0 < Z ∧ Z⁻¹ ≤ 2) ∧
        ∃ (hN : ∀ t, 0 < N t) (modulus : ℕ) (hmodulus : 0 < modulus),
        let : NeZero modulus := ⟨hmodulus.ne'⟩
        modulus ≤ M^(m+1) ∧
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
        ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
          (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
        let refined := residueRefinedPeriod modulus stride
        (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
        ∃ hRefined : 0 < refined,
        let : NeZero refined := ⟨hRefined.ne'⟩
        (∀ t, stride t * modulus ∣ refined) ∧
        (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*Pc + Fintype.card X*T) ∧
        ∃ hlengths : ∀ t, (Fintype.card (Fin dim)+1)*refined ≤
          principalAxisLength (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S) t,
        ∃ (reference : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
              (allocatedPrincipalSides B U b S) →
            (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
              (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
            PrincipalAxisTuples (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
              (allocatedPrincipalSides B U b S))
          (residue : PrincipalAxisTuples (α := Fin dim) (allocatedGridAxis (I := I) U b S.value)
              (allocatedPrincipalSides B U b S) →
            (PrincipalTupleIndex (fun a : {a // ¬allocatedGridAxis (I := I) U b S.value a} => B a.val)
              (fun a => layerSamplerDegree I n a.val) → Option (Fin dim) → ZMod refined) →
            ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        (∀ u r, principalResidueLabel refined (reference u r) = r) ∧
        (∀ u r v, (allocatedLongResidueWeights B U b S refined hRefined r hlengths).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue u r j) ∧
        ‖allocatedRefinedTupleDifference B U b hR hσ S x rows X hM selection hx modulus s hA
          stride reference residue hb o bW d g N hN hW hτ hξ mesh base cells hmass
          (physicalCubeEuclideanSample U d poly hmem) test Z‖ ≤ Real.exp (-Etarget)
      )

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedSpatiallyNormalizedTupleComparison (m dim : ℕ) :
    allocatedSpatiallyNormalizedTupleStatement m dim := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedActualNormalizedTupleComparison m dim
  unfold allocatedSpatiallyNormalizedTupleStatement
  refine ⟨A, Amass, hA, hAmass, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hG hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, ?_⟩
  intro hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ p Etarget hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp hmsp ξ₀ hξ D hD Perr Pmass hPerr hAccuracy hQ
    hnormdim poly hpoly hmem N stride hs Rrank W τ hW hτ l δ mesh
    hWScale hWP hξP hτP hstride hsize hrank hRank hspatialSize
    hbudget base cells hcells bases hbases
    test htest Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  let C₀ := 1 + (S.value : ℝ) + W
  let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection M p Etarget C₀ W cap (allocatedPhysicalEntryBudget B U b S (fun _ => 0))
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_le_of_embedding
      (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B))).trans hvarsp
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p := by
    have h : ((dim + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : dim + 1 ≤ m + 2)
    exact h.trans hmsp
  have hentry : 0 ≤ allocatedPhysicalEntryBudget B U b S (fun _ => 0) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  obtain ⟨_, _, _, hPerrBudget⟩ :=
    allocatedScalarSamplingBudget_bounds m dim A hP (hP.trans hPerr)
  have hPPmass : P ≤ Pmass := hPerr.trans (hPerrBudget.trans hQ)
  obtain ⟨hl, hMassl, hC₀, hLC, hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    allocatedSpatialLateInputBounds B U b S C V hP hPPmass hm hvars hR hσ hRP hσP
      hcount hI hn hJ hAP hL hCP hVP hW hWP
  have hspatial (t : X) : 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ) := by
    exact normalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      hp hEtarget hl hM hmsp' hdimsp hGp hXp hMp (by linarith) hW hcap hentry
      hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _)
      ((hstride t).trans (Real.exp_le_exp.mpr hMassl)) hτ
      (by simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr hMassl)) (hspatialSize t)
  obtain ⟨_, hξ1, _, hchoices⟩ := normalizedTupleSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hp hEtarget hmsp' hdimsp hGp hXp hMp
  obtain ⟨hδ, _, hmesh, hρ, hmeshSize, hρ8, hρshift, hρmove, hboundary, hsite⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := (S.value : ℝ)) (Cg := cap)
      (Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0))
      (by linarith) hW (by exact_mod_cast S.positive) hcap hentry hD hWScale
  have hρshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hρshift
  have hEplus : 0 ≤ Etarget + 2 := by linarith
  have heq : (Etarget + 2) + 1 = Etarget + 3 := by ring
  have hAccuracy' : allocatedCoefficientAccuracyLog m p ((Etarget + 2) + 1) ≤ Perr := by
    simpa only [heq] using hAccuracy
  have hlarge' := hlarge
  rw [← heq] at hlarge'
  obtain ⟨hmass, hnormal, hN, modulus, hmodulus, hrest⟩ :=
    hdata hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hp hEplus
      hvarsp hIp hnp hJp hXp hCp hMp hD hPerr hAccuracy' hQ hnormdim
      poly hpoly hmem N stride hs hW hτ hξ hξ1 hρ hWScale hWP hξP hτP hstride
      hsize hrank hRank hspatial hρ8 hρshift' hbudget hC₀ hLC hWC hmeshSize
      hδ.le hρmove hmesh base cells hcells bases hbases test htest bW
      hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge'
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hrest⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ := hrest
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  exact allocatedRefinedTupleDifference_exp_bound B U b hR hσ S x rows X hM selection hx
    modulus s hsA stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh
    base cells hmass (physicalCubeEuclideanSample U d poly hmem) test cap Z
    hnormal.2.1.1 hcompare hboundary (hsite modulus hmod)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedSpatiallyNormalizedTupleComparison_withProjection (m dim : ℕ) :
    allocatedSpatiallyNormalizedTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedActualNormalizedTupleComparison_withProjection m dim
  unfold allocatedSpatiallyNormalizedTupleStatement
  refine ⟨A, Amass, hA, hAmass, ?_⟩
  intro G _ _ I _ _ n B _ _ J _ U b R σ S x P hP hG hL M hM selection hx hdim
  obtain ⟨d, hd, hdb, hconstruct⟩ := hactual B U b S x hP hG hL hM selection hx hdim
  let : NeZero d := ⟨hd.ne'⟩
  refine ⟨d, hd, hdb, ?_⟩
  intro _ _ _ _ _ hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ _ _ ν _ _
    O rows density cap cover ξ
  obtain ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, hdata⟩ :=
    hconstruct hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall μ ν
  refine ⟨g, hgc, hgb, hgi, hgm, hglaw, hprojection, ?_⟩
  intro hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP X _ _ p Etarget hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp hmsp ξ₀ hξ D hD Perr Pmass hPerr hAccuracy hQ
    hnormdim poly hpoly hmem N stride hs Rrank W τ hW hτ l δ mesh
    hWScale hWP hξP hτP hstride hsize hrank hRank hspatialSize
    hbudget base cells hcells bases hbases
    test htest Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  let C₀ := 1 + (S.value : ℝ) + W
  let ρ := normalizedTupleResolution X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection M p Etarget C₀ W cap (allocatedPhysicalEntryBudget B U b S (fun _ => 0))
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (Fintype.card_le_of_embedding
      (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B))).trans hvarsp
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p := by
    have h : ((dim + 1 : ℕ) : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : dim + 1 ≤ m + 2)
    exact h.trans hmsp
  have hentry : 0 ≤ allocatedPhysicalEntryBudget B U b S (fun _ => 0) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (allocatedPhysicalEntryBudget_one_le B U b S (fun _ => 0))
  have hcap : 0 ≤ cap := by dsimp [cap]; positivity
  obtain ⟨_, _, _, hPerrBudget⟩ :=
    allocatedScalarSamplingBudget_bounds m dim A hP (hP.trans hPerr)
  have hPPmass : P ≤ Pmass := hPerr.trans (hPerrBudget.trans hQ)
  obtain ⟨hl, hMassl, hC₀, hLC, hWC, hC₀l, hcapl, hentryl, hWl, hprofilel⟩ :=
    allocatedSpatialLateInputBounds B U b S C V hP hPPmass hm hvars hR hσ hRP hσP
      hcount hI hn hJ hAP hL hCP hVP hW hWP
  have hspatial (t : X) : 8 * (1 + W) * (stride t : ℝ) * ρ ≤ (ξ₀ * τ) * (N t : ℝ) := by
    exact normalizedTupleSpatialSize X (PrincipalTupleIndex B (layerSamplerDegree I n)) selection
      hp hEtarget hl hM hmsp' hdimsp hGp hXp hMp (by linarith) hW hcap hentry
      hC₀l hWl hcapl hentryl hprofilel (Nat.cast_nonneg _)
      ((hstride t).trans (Real.exp_le_exp.mpr hMassl)) hτ
      (by simpa only [one_div] using hτP.trans (Real.exp_le_exp.mpr hMassl)) (hspatialSize t)
  obtain ⟨_, hξ1, _, hchoices⟩ := normalizedTupleSpatialChoices
    (N := PrincipalTupleIndex B (layerSamplerDegree I n)) (X := X) (m := m)
    selection hM hp hEtarget hmsp' hdimsp hGp hXp hMp
  obtain ⟨hδ, _, hmesh, hρ, hmeshSize, hρ8, hρshift, hρmove, hboundary, hsite⟩ :=
    hchoices (C₀ := C₀) (W := W) (L := (S.value : ℝ)) (Cg := cap)
      (Centry := allocatedPhysicalEntryBudget B U b S (fun _ => 0))
      (by linarith) hW (by exact_mod_cast S.positive) hcap hentry hD hWScale
  have hρshift' : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ := by
    simpa only [mul_assoc] using hρshift
  have hEplus : 0 ≤ Etarget + 2 := by linarith
  have heq : (Etarget + 2) + 1 = Etarget + 3 := by ring
  have hAccuracy' : allocatedCoefficientAccuracyLog m p ((Etarget + 2) + 1) ≤ Perr := by
    simpa only [heq] using hAccuracy
  have hlarge' := hlarge
  rw [← heq] at hlarge'
  obtain ⟨hmass, hnormal, hN, modulus, hmodulus, hrest⟩ :=
    hdata hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hp hEplus
      hvarsp hIp hnp hJp hXp hCp hMp hD hPerr hAccuracy' hQ hnormdim
      poly hpoly hmem N stride hs hW hτ hξ hξ1 hρ hWScale hWP hξP hτP hstride
      hsize hrank hRank hspatial hρ8 hρshift' hbudget hC₀ hLC hWC hmeshSize
      hδ.le hρmove hmesh base cells hcells bases hbases test htest bW
      hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge'
  let : NeZero modulus := ⟨hmodulus.ne'⟩
  obtain ⟨hmod, hspatialPeriod, hperiod, s, hsA, hi, hrest⟩ := hrest
  obtain ⟨hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, hcompare⟩ := hrest
  let : NeZero (residueRefinedPeriod modulus stride) := ⟨hRefined.ne'⟩
  refine ⟨hmass, hnormal, hN, modulus, hmodulus, hmod, hspatialPeriod, hperiod,
    s, hsA, hi, hRefined, hdiv, hbound, hlengths, reference, residue, href, hr, ?_⟩
  exact allocatedRefinedTupleDifference_exp_bound B U b hR hσ S x rows X hM selection hx
    modulus s hsA stride reference residue hb o bW d g N hN hW hτ hξ C₀ ρ δ mesh
    base cells hmass (physicalCubeEuclideanSample U d poly hmem) test cap Z
    hnormal.2.1.1 hcompare hboundary (hsite modulus hmod)

end Erdos3.VectorPolynomial

end

end OAI
