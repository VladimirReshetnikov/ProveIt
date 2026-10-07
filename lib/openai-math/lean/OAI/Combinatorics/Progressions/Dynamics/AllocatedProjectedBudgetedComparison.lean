import OAI.Combinatorics.Progressions.Sampling.AllocatedUnifiedSamplingBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory Polynomial
open scoped BigOperators Classical NNReal

universe uX

def allocatedBudgetedTupleStatement (m dim : ℕ) (keepProjection : Bool := false) : Prop :=
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
        ∀ {D : ℝ} (_hD : D ≤ Real.exp p),
        let Perr := allocatedTupleErrorBudget m P p Etarget
        let Pmass := allocatedUnifiedSamplingBudget m dim A P p Etarget
        ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
        (_hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
        (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
        (N stride : X → ℕ) (_hs : ∀ t, 0 < stride t)
        {Rrank W τ : ℝ}
        (hW : 0 ≤ W) (hτ : 0 < τ),
        let δ := normalizedTupleRadius X selection M p Etarget W
        let mesh := δ / 4
        ∀ (_hWScale : W ≤ D * S.value)
        (_hτP : 1 / τ ≤ Real.exp Pmass) (_hstride : ∀ t, (stride t : ℝ) ≤ Real.exp Pmass)
        (_hsize : ∀ t, Real.exp ((P + p + Etarget + Amass) ^ Amass) ≤ (N t : ℝ))
        (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) Rrank (U j) (poly j))
        (_hRank : Real.exp ((P + p + Etarget + Amass) ^ Amass) ≤ Rrank)
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

theorem allocatedBudgetedTupleComparison (m dim : ℕ) :
    allocatedBudgetedTupleStatement m dim := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedSpatiallyNormalizedTupleComparison m dim
  obtain ⟨bside, hbside, hside⟩ := exists_allocatedTupleSideThreshold_bound m
  let K := max Amass bside
  obtain ⟨a, ha, hcut⟩ := exists_allocatedUnifiedSamplingThreshold_bound m dim A K
  unfold allocatedBudgetedTupleStatement
  refine ⟨A, a, hA, ha, ?_⟩
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
    hvarsp hIp hnp hJp hXp hCp hMp hmsp ξ₀ hξ D hD Perr Pmass
    poly hpoly hmem N stride hs Rrank W τ hW hτ δ mesh
    hWScale hτP hstride hsize hrank hRank hbudget base cells hcells bases hbases
    test htest Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  obtain ⟨_, hPerr, hAccuracy, hQ0, hQ, hwidth, hPplus, hpQ, hEQ, hnorm⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hEtarget
  have hPPmass : P ≤ Pmass := by linarith
  have hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmass := by
    calc
      _ = ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * Fintype.card X := by
        simp only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ (p + 1) * p := mul_le_mul (add_le_add hvarsp le_rfl) hXp (Nat.cast_nonneg _) (by positivity)
      _ = p * (p + 1) := mul_comm _ _
      _ ≤ _ := hnorm
  have hWP : W ≤ Real.exp Pmass := by
    calc
      _ ≤ D * S.value := hWScale
      _ ≤ Real.exp p * Real.exp P := mul_le_mul hD hL (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (P + p) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hPplus
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsp
  have hNp : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvarsp
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim + 1 ≤ m + 2)).trans hmsp
  have hqcard : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdimsp
  have hchoice := normalizedTupleSpatialChoices (N := PrincipalTupleIndex B (layerSamplerDegree I n))
    (X := X) (m := m) selection hM hp hEtarget hmsp' hdimsp hGp hXp hMp
  have hlog := (normalizedTuple_log_envelopes X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection hp hEtarget (le_refl (0 : ℝ)) hqcard hGp hNp hXp).1
  have hξP : ξ₀⁻¹ ≤ Real.exp Pmass :=
    hchoice.2.2.1.trans (Real.exp_le_exp.mpr (hlog.trans hwidth))
  have hcut' := hcut hP hp hEtarget
  have hmassCut : (Pmass + Amass) ^ Amass ≤ (P + p + Etarget + a) ^ a :=
    (shifted_power_self_mono hQ0 (by omega) (le_max_left Amass bside)).trans hcut'
  have hsideCut := hside B X selection hP hQ0 hp hEtarget hPPmass hpQ hEQ hvarsp hXp hqcard
  have hsideCut' : normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection p Etarget (allocatedSpatialLateLog (G := G) B P Pmass) ≤
        (P + p + Etarget + a) ^ a :=
    hsideCut.trans ((shifted_power_self_mono hQ0 (by omega) (le_max_right Amass bside)).trans hcut')
  exact hdata hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp hmsp hD hPerr hAccuracy hQ hnormdim
    poly hpoly hmem N stride hs hW hτ hWScale hWP hξP hτP hstride
    (fun t => (Real.exp_le_exp.mpr hmassCut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hmassCut).trans hRank)
    (fun t => (Real.exp_le_exp.mpr hsideCut').trans (hsize t)) hbudget base cells hcells bases hbases
    test htest bW hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem allocatedBudgetedTupleComparison_withProjection (m dim : ℕ) :
    allocatedBudgetedTupleStatement m dim true := by
  obtain ⟨A, Amass, hA, hAmass, hactual⟩ := allocatedSpatiallyNormalizedTupleComparison_withProjection m dim
  obtain ⟨bside, hbside, hside⟩ := exists_allocatedTupleSideThreshold_bound m
  let K := max Amass bside
  obtain ⟨a, ha, hcut⟩ := exists_allocatedUnifiedSamplingThreshold_bound m dim A K
  unfold allocatedBudgetedTupleStatement
  refine ⟨A, a, hA, ha, ?_⟩
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
    hvarsp hIp hnp hJp hXp hCp hMp hmsp ξ₀ hξ D hD Perr Pmass
    poly hpoly hmem N stride hs Rrank W τ hW hτ δ mesh
    hWScale hτP hstride hsize hrank hRank hbudget base cells hcells bases hbases
    test htest Kcov _ bW Pc T hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge
    widths baseDensity Z
  obtain ⟨_, hPerr, hAccuracy, hQ0, hQ, hwidth, hPplus, hpQ, hEQ, hnorm⟩ :=
    allocatedUnifiedSamplingBudget_bounds m dim A hP hp hEtarget
  have hPPmass : P ≤ Pmass := by linarith
  have hnormdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Pmass := by
    calc
      _ = ((Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 1) * Fintype.card X := by
        simp only [Fintype.card_prod, Fintype.card_option, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      _ ≤ (p + 1) * p := mul_le_mul (add_le_add hvarsp le_rfl) hXp (Nat.cast_nonneg _) (by positivity)
      _ = p * (p + 1) := mul_comm _ _
      _ ≤ _ := hnorm
  have hWP : W ≤ Real.exp Pmass := by
    calc
      _ ≤ D * S.value := hWScale
      _ ≤ Real.exp p * Real.exp P := mul_le_mul hD hL (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp (P + p) := by rw [← Real.exp_add, add_comm]
      _ ≤ _ := Real.exp_le_exp.mpr hPplus
  have hGp : (Fintype.card G : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hvarsp
  have hNp : (Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (allocatedPrincipalIndex_card_le_variables (G := G) B)).trans hvarsp
  have hmsp' : ((m + 1 : ℕ) : ℝ) ≤ p := by push_cast at hmsp ⊢; linarith
  have hdimsp : ((dim + 1 : ℕ) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (by omega : dim + 1 ≤ m + 2)).trans hmsp
  have hqcard : (Fintype.card (Unit ⊕ Fin dim) : ℝ) ≤ p := by
    simpa only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin, Nat.add_comm 1] using hdimsp
  have hchoice := normalizedTupleSpatialChoices (N := PrincipalTupleIndex B (layerSamplerDegree I n))
    (X := X) (m := m) selection hM hp hEtarget hmsp' hdimsp hGp hXp hMp
  have hlog := (normalizedTuple_log_envelopes X (PrincipalTupleIndex B (layerSamplerDegree I n))
    selection hp hEtarget (le_refl (0 : ℝ)) hqcard hGp hNp hXp).1
  have hξP : ξ₀⁻¹ ≤ Real.exp Pmass :=
    hchoice.2.2.1.trans (Real.exp_le_exp.mpr (hlog.trans hwidth))
  have hcut' := hcut hP hp hEtarget
  have hmassCut : (Pmass + Amass) ^ Amass ≤ (P + p + Etarget + a) ^ a :=
    (shifted_power_self_mono hQ0 (by omega) (le_max_left Amass bside)).trans hcut'
  have hsideCut := hside B X selection hP hQ0 hp hEtarget hPPmass hpQ hEQ hvarsp hXp hqcard
  have hsideCut' : normalizedTupleSideLog X (PrincipalTupleIndex B (layerSamplerDegree I n))
      selection p Etarget (allocatedSpatialLateLog (G := G) B P Pmass) ≤
        (P + p + Etarget + a) ^ a :=
    hsideCut.trans ((shifted_power_self_mono hQ0 (by omega) (le_max_right Amass bside)).trans hcut')
  exact hdata hm hvars hRP hσP hcount hI hn hJ hAP hCP hVP hp hEtarget
    hvarsp hIp hnp hJp hXp hCp hMp hmsp hD hPerr hAccuracy hQ hnormdim
    poly hpoly hmem N stride hs hW hτ hWScale hWP hξP hτP hstride
    (fun t => (Real.exp_le_exp.mpr hmassCut).trans (hsize t)) hrank
    ((Real.exp_le_exp.mpr hmassCut).trans hRank)
    (fun t => (Real.exp_le_exp.mpr hsideCut').trans (hsize t)) hbudget base cells hcells bases hbases
    test htest bW hPc hPcErr hT hMP hRupper hRi hσi hcountc hstridec hlarge

end Erdos3.VectorPolynomial

end

end OAI
