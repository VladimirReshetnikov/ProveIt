/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Set
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativeFinalPower
import OAI.Combinatorics.Progressions.Sampling.PrecenterForecastNativePartners
import OAI.Combinatorics.Progressions.Sampling.PreparedCenteredShortForecastProductiveGoodModel

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

def AllocatedPathProductivity {nX : ℕ}
    (N : Fin nX → ℕ)
    (widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)) (test : (Fin nX → ℝ) → ℝ) (gain : ℝ)
    (z : bases × rectangularWeightIndices 0 widths 1) : Prop :=
  let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
  let Sites := integerBox sides
  Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val, z.2.val)) ∧
    (gain / 2 ≤ 𝔼 q : Sites, test
      (fun i => (jointIntegerPhysicalSite q.val (z.1.val, z.2.val) i : ℝ))) ∧
    ∀ q : Sites, jointIntegerPhysicalSite q.val (z.1.val, z.2.val) ∈ integerBox N

theorem preparedCenteredProductive_event
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    {nX : ℕ} (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hm : ∀ j d, coefficients (poly j) d ∈ U j)
    (N : Fin nX → ℕ)
    (widths : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)) (gainLog : ℝ)
    (law : CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 widths 1))
    (hproductive : PreparedCenteredForecastProductiveConclusion B U basis S hb o hR hσ
      μ poly hm N widths bases gainLog law)
    (test : (Fin nX → ℝ) → ℝ) (htest : ∀ x, |test x| ≤ 1)
    (gain : ℝ) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    let joint := centeredFiniteProbabilityMeasure μ law
    IsProbabilityMeasure joint ∧
      MeasurableSet {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
        (bases × rectangularWeightIndices 0 widths 1) |
        AllocatedPathProductivity B U basis S N widths bases test gain z.2} ∧
      gain / 4 ≤ joint.real {z | AllocatedPathProductivity B U basis S N widths bases test gain z.2} ∧
      ∀ᵐ z ∂joint, ∃ c : ∀ j, U j,
        coefficientConstantCenter U z.1 =
          -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
            (constantCoefficientArray U (fun a => c a.1))) ∧
        allocatedAffineDensity B U basis hb o hR hσ S poly hm c
          (fun k v => (jointIntegerFrame (z.2.1.val, z.2.2.val) k v : ℝ)) ≠ 0 := by
  intro joint
  obtain ⟨hprob, hmeas, hmass, hnonzero, hphysical⟩ :=
    hproductive test htest gain hgain hmean
  let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
  let Sites := integerBox sides
  let productive := Finset.univ.filter (fun z : bases × rectangularWeightIndices 0 widths 1 =>
    Function.Injective (fun q : Sites => jointIntegerPhysicalSite q.val (z.1.val, z.2.val)) ∧
      gain / 2 ≤ 𝔼 q : Sites, test
        (fun i => (jointIntegerPhysicalSite q.val (z.1.val, z.2.val) i : ℝ)))
  have hevent :
      {z : CoefficientTorus (K := LayerSamplerVariables G I n B) U ×
          (bases × rectangularWeightIndices 0 widths 1) |
        AllocatedPathProductivity B U basis S N widths bases test gain z.2} =
      {z | z.2 ∈ productive} := by
    ext z
    simp only [Set.mem_ofPred_eq, AllocatedPathProductivity, productive,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hinj, hscore, _⟩
      exact ⟨hinj, hscore⟩
    · rintro ⟨hinj, hscore⟩
      exact ⟨hinj, hscore, hphysical z.2⟩
  exact ⟨hprob, hevent.symm ▸ hmeas, hevent.symm ▸ hmass, hnonzero⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredFiniteProductiveGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∀ (residual : Set (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1))),
          MeasurableSet residual → (centeredFiniteProbabilityMeasure μ law).real residual ≤ gain / 32 →
        ∀ (Extra : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → Prop),
          (∀ᵐ z ∂centeredFiniteProbabilityMeasure μ law, Extra z) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧ (center,z) ∉ residual ∧ Extra (center,z) ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

theorem preparedCenteredFiniteProductiveGood
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    PreparedCenteredFiniteProductiveGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test := by
  classical
  unfold PreparedCenteredFiniteProductiveGoodConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hbad⟩ := hgood
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth residual hResidual hResidualMass Extra hExtra
  obtain ⟨bad, hbadMeas, hbadMass, hgoodAE⟩ := hbad primes hprime depth hdepth
  obtain ⟨hprob, hproductiveMeas, hproductiveMass, hnonzero⟩ :=
    preparedCenteredProductive_event (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S hb o hR hσ
      μ poly hm N width bases gainLog law hproductive test htest gain hgain hmean
  have hgainPos : 0 < gain := (Real.exp_pos _).trans_le hgain
  have hbadMass' : (centeredFiniteProbabilityMeasure μ law).real bad ≤ gain / 16 := by
    linarith only [hbadMass]
  have hAE := hgoodAE.and (hnonzero.and hExtra)
  have hsel := exists_center_finite_productive_good_event_avoiding_residual μ law hweight
  have hsel := hsel _ hproductiveMeas bad hbadMeas residual hResidual
  have hsel := hsel _ hAE hgainPos
  obtain ⟨center, F, hmass, hF⟩ := hsel hproductiveMass hbadMass' hResidualMass
  refine ⟨center, F, hmass, ?_⟩
  intro z hz
  obtain ⟨hzprod, hzbad, hzresidual, hzweight, hzgood, hzdensity, hzextra⟩ := hF z hz
  have hRecovered := hzgood hzbad
  exact ⟨hzweight, hzresidual, hzextra, hzprod, hzdensity, hRecovered⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredFiniteModelProductiveGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (_μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    {Tmodel Xmodel Branch : Type*} [Fintype Tmodel] [Fintype Branch]
    {Tests : (bases × rectangularWeightIndices 0 width 1) → Type*}
    (physicalModel : (bases × rectangularWeightIndices 0 width 1) → Tmodel → Xmodel)
    (slicesModel : ∀ z, Tests z → Finset Tmodel)
    (testsModel : ∀ z, Tests z → Tmodel → ℂ)
    (models : Branch → CenteredForecastModel Xmodel) (Eres : ℝ) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧
            (∀ branch j, ‖𝔼 t ∈ slicesModel z j,
              (models branch).residual (physicalModel z t) * testsModel z j t‖ ≤ Real.exp (-Eres)) ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

theorem preparedCenteredFiniteModelProductiveGood
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))
    {Tmodel Xmodel Forecast Branch : Type*}
    [Fintype Tmodel] [Nonempty Tmodel] [Fintype Xmodel] [Fintype Branch]
    {Tests : (bases × rectangularWeightIndices 0 width 1) → Type*}
    (physicalModel : (bases × rectangularWeightIndices 0 width 1) → Tmodel → Xmodel)
    (slicesModel : ∀ z, Tests z → Finset Tmodel)
    (testsModel : ∀ z, Tests z → Tmodel → ℂ) {Kmodel : ℝ}
    (hSlices : ∀ z j, (slicesModel z j).Nonempty)
    (hSize : ∀ z j, (Fintype.card Tmodel : ℝ) / (slicesModel z j).card ≤ Kmodel)
    (hTests : ∀ z j t, ‖testsModel z j t‖ ≤ 1)
    (nativeModel : Set (Xmodel → ℂ)) (referenceModel : FiniteProbabilityWeights Xmodel)
    (forecastModel : Forecast → Xmodel → ℂ)
    (selectedLocal : (Xmodel → ℂ) → (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U × (bases × rectangularWeightIndices 0 width 1) → ℂ) → Prop)
    (inputModels : Branch → Xmodel → ℂ) (coefficientBound termBound : ℝ)
    (models : Branch → CenteredForecastModel Xmodel)
    {uModelError Eres Bbranch : ℝ}
    (hmodels : ∀ branch, CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ law)
      nativeModel referenceModel forecastModel
      (sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
        physicalModel slicesModel testsModel)
      selectedLocal (inputModels branch) coefficientBound (Real.exp (-uModelError))
        termBound (models branch))
    (hBranch : (Fintype.card Branch : ℝ) ≤ Real.exp Bbranch)
    (hErrorBudget : Bbranch + gainLog + Eres + 6 ≤ uModelError) :
    PreparedCenteredFiniteModelProductiveGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
      physicalModel slicesModel testsModel models Eres := by
  classical
  obtain ⟨hResidualMeas, hResidualMass, hUniform⟩ :=
    centeredFiniteForecastModels_uniformResidualBadSet μ law hweight
      physicalModel slicesModel testsModel hSlices hSize hTests
      nativeModel referenceModel forecastModel selectedLocal inputModels coefficientBound termBound
      models hmodels hBranch hgain hErrorBudget
  have hselected := preparedCenteredFiniteProductiveGood (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
    hweight hgood hproductive htest hgain hmean
  unfold PreparedCenteredFiniteModelProductiveGoodConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hfinite⟩ := hselected
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  obtain ⟨center, F, hmass, hF⟩ :=
    hfinite primes hprime depth hdepth _ hResidualMeas hResidualMass
      (fun _ => True) (ae_of_all _ (fun _ => True.intro))
  refine ⟨center, F, hmass, ?_⟩
  intro z hz
  obtain ⟨hpos, havoid, _, hprod, hdensity, hrec, hmod, hdet⟩ := hF z hz
  have herror := hUniform (center,z) havoid
  exact ⟨hpos, herror, hprod, hdensity, hrec, hmod, hdet⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredProductiveGoodCenterConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (_μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

theorem preparedCenteredProductiveGoodCenter
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) :
    PreparedCenteredProductiveGoodCenterConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test := by
  classical
  have hselected := preparedCenteredFiniteProductiveGood (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
    hweight hgood hproductive htest hgain hmean
  unfold PreparedCenteredProductiveGoodCenterConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hfinite⟩ := hselected
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  have hgainNonneg : 0 ≤ gain := (Real.exp_nonneg _).trans hgain
  obtain ⟨center, F, hmass, hF⟩ :=
    hfinite primes hprime depth hdepth ∅ MeasurableSet.empty
      (by simpa using (div_nonneg hgainNonneg (by norm_num : (0 : ℝ) ≤ 32)))
      (fun _ => True) (ae_of_all _ (fun _ => True.intro))
  refine ⟨center, F, hmass, ?_⟩
  intro z hz
  obtain ⟨hpos, _, _, hprod, hdensity, hrec, hmod, hdet⟩ := hF z hz
  exact ⟨hpos, hprod, hdensity, hrec, hmod, hdet⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal

def PreparedCenteredStagedModelProductiveGoodConclusion
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (_μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    {Tmodel Xmodel Stage : Type*} [Fintype Tmodel] [Fintype Stage]
    {Branch : Stage → Type*} [∀ k, Fintype (Branch k)]
    {Tests : Stage → (bases × rectangularWeightIndices 0 width 1) → Type*}
    (physicalModel : (bases × rectangularWeightIndices 0 width 1) → Tmodel → Xmodel)
    (slicesModel : ∀ k z, Tests k z → Finset Tmodel)
    (testsModel : ∀ k z, Tests k z → Tmodel → ℂ)
    (models : ∀ k, Branch k → CenteredForecastModel Xmodel) (Eres : Stage → ℝ) : Prop :=
    ∃ (c : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → ∀ j, U j), Measurable c ∧
      (∀ center, coefficientConstantCenter U center =
        -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c center s.1)))) ∧
    ∃ (sample : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) →
          CoefficientSamplerArrays (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep))
      (read : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U → (Fin nX → ℤ) → (Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℤ) → AllocatedActualCoefficientIndex (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (Fin nX) (PreparedSamplerContinuous prep) E (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) → ℤ),
      (∀ center a, AllocatedCenteredRecoveredSampleReadAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U bW b hb o S hR hσ poly hm (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) (modularInitialRankStrength m (nX + m * M) : ℝ) center (c center) a (sample center a) (read center a)) ∧
      ∀ (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime),
        letI : ∀ p : primes, NeZero p.val := fun p => ⟨(hprime p.val p.property).ne_zero⟩
        ∀ (depth : ℕ → ℕ), (∀ p ∈ primes, p ^ depth p ≤ Q) →
        ∃ (center : CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) (F : Finset (bases × rectangularWeightIndices 0 width 1)),
          gain / 16 < (law center).mass F ∧
          ∀ z ∈ F, 0 < (law center).weight z ∧
            (∀ stage branch j, ‖𝔼 t ∈ slicesModel stage z j,
              (models stage branch).residual (physicalModel z t) * testsModel stage z j t‖ ≤
                Real.exp (-Eres stage)) ∧
            AllocatedPathProductivity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S N width bases test gain z ∧
            (∃ c₀ : ∀ j, U j, coefficientConstantCenter U center =
              -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
                (constantCoefficientArray U (fun s => c₀ s.1))) ∧
              allocatedAffineDensity (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o hR hσ S poly hm c₀
                (fun k v => (jointIntegerFrame (z.1.val,z.2.val) k v : ℝ)) ≠ 0) ∧
            AllocatedCenteredFramedRecoveredSampleAt (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b hb o S hR hσ poly hm
              (c center) z.1.val z.2.val (sample center z.1.val z.2.val) (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val)) ∧
            (∏ p ∈ primes, p ^ largestTestedBadDepth depth (allocatedActualPrimeBad (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value) (preparedInitialRankSpatialEmbedding (m := m) nX M) (preparedInitialRankKernelEmbedding (m := m) nX M) (preparedInitialRankPrincipalEmbedding prep nX M (allocatedShortAxis (I := PreparedSamplerContinuous prep) U b S.value)) primes (modularInitialRankStrength m (nX + m * M) : ℝ)) p (allocatedJointFrameRead z.1.val (read center z.1.val z.2.val))) ≤ (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) * quantitativeBadPrimeRadius (gainLog + 8)) ∧
            ∀ t : Fin 2, spatialMatrixBlockThreshold nX (jointSpatialError gainLog) / 2 <
              |Matrix.det (fun i j : Fin nX =>
                spatialMatrixNormalizedEntries e width z.2.val (t,j,i))|

theorem preparedCenteredStagedModelProductiveGood
    {m nX M : ℕ} {X₀ J₀ : Type}
    (prep : RankPreparationFamily X₀ J₀ m)
    (U : ∀ j : Fin m, Submodule ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (b : ∀ j, Basis (Fin (preparedSamplerTransverse prep j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ}
    (S : LayerSamplerScale (G := EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (I := PreparedSamplerContinuous prep) (n := preparedSamplerTransverse prep)
      (J := fun j : Fin m => RankPreparationLayer.Coord (prep j)) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b R σ)
    {E : Fin m → Type} [∀ j, Fintype (E j)]
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (RankPreparationLayer.Coord (prep j))) (euclideanSubspace (U j))))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous prep j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (RankPreparationLayer.Coord (prep j) → ℝ))
    (hm : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (stride : Fin nX → ℕ)
    (width : Option (LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ))
    (gainLog gain : ℝ) (Q : ℕ)
    (e : Fin 2 × Fin nX ↪ EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M)))
    (law : (CoefficientTorus (K := LayerSamplerVariables (EnlargedPreparedCommonKernel m (modularInitialBlockCount m (nX + m * M))) (PreparedSamplerContinuous prep) (preparedSamplerTransverse prep) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M)))) U) → FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1))
    (N : Fin nX → ℕ) (test : (Fin nX → ℝ) → ℝ)
    [IsProbabilityMeasure μ]
    (hweight : ∀ z, Measurable (fun center => (law center).weight z))
    (hgood : PreparedCenteredShortForecastGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law)
    (hproductive : PreparedCenteredForecastProductiveConclusion (nX := nX) (EnlargedPreparedCommonSamplerBlock prep (modularInitialBlockCount m (nX + m * M))) U b S
      hb o hR hσ μ poly hm N width bases gainLog law)
    (htest : ∀ x, |test x| ≤ 1) (hgain : Real.exp (-gainLog) ≤ gain)
    (hmean : gain ≤ 𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ)))
    {Tmodel Xmodel Stage : Type*}
    [Fintype Tmodel] [Nonempty Tmodel] [Fintype Stage]
    {Branch : Stage → Type*} [∀ k, Fintype (Branch k)]
    {Tests : Stage → (bases × rectangularWeightIndices 0 width 1) → Type*}
    (physicalModel : (bases × rectangularWeightIndices 0 width 1) → Tmodel → Xmodel)
    (slicesModel : ∀ k z, Tests k z → Finset Tmodel)
    (testsModel : ∀ k z, Tests k z → Tmodel → ℂ) {Kmodel : Stage → ℝ}
    (hSlices : ∀ k z j, (slicesModel k z j).Nonempty)
    (hSize : ∀ k z j, (Fintype.card Tmodel : ℝ) / (slicesModel k z j).card ≤ Kmodel k)
    (hTests : ∀ k z j t, ‖testsModel k z j t‖ ≤ 1)
    (models : ∀ k, Branch k → CenteredForecastModel Xmodel)
    (uModelError Bbranch Eres : Stage → ℝ) {stageLog : ℝ}
    (hLocalResidual : ∀ k branch,
      sampledSliceSeminorm (centeredFiniteMarginal μ law hweight)
        physicalModel (slicesModel k) (testsModel k) (models k branch).residual ≤
          Real.exp (-uModelError k))
    (hBranch : ∀ k, (Fintype.card (Branch k) : ℝ) ≤ Real.exp (Bbranch k))
    (hStageCount : (Fintype.card Stage : ℝ) + 1 ≤ Real.exp stageLog)
    (hErrorBudget : ∀ k, Bbranch k + gainLog + Eres k + stageLog + 6 ≤ uModelError k) :
    PreparedCenteredStagedModelProductiveGoodConclusion (m := m) (nX := nX) (M := M)
      prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
      physicalModel slicesModel testsModel models Eres := by
  classical
  obtain ⟨hResidualMeas, hResidualMass, hUniform⟩ :=
    centeredStagedForecastModels_uniformResidualBadSet μ law hweight
      physicalModel slicesModel testsModel hSlices hSize hTests
      models uModelError Bbranch Eres hLocalResidual hBranch hgain hStageCount hErrorBudget
  have hselected := preparedCenteredFiniteProductiveGood (m := m) (nX := nX) (M := M)
    prep U b S bW hb o hR hσ μ poly hm stride width bases gainLog gain Q e law N test
    hweight hgood hproductive htest hgain hmean
  unfold PreparedCenteredStagedModelProductiveGoodConclusion
  obtain ⟨c, hc, hcenter, sample, read, hread, hfinite⟩ := hselected
  refine ⟨c, hc, hcenter, sample, read, hread, ?_⟩
  intro primes hprime depth hdepth
  obtain ⟨center, F, hmass, hF⟩ :=
    hfinite primes hprime depth hdepth _ hResidualMeas hResidualMass
      (fun _ => True) (ae_of_all _ (fun _ => True.intro))
  refine ⟨center, F, hmass, ?_⟩
  intro z hz
  obtain ⟨hpos, havoid, _, hprod, hdensity, hrec, hmod, hdet⟩ := hF z hz
  have herror := hUniform (center,z) havoid
  exact ⟨hpos, herror, hprod, hdensity, hrec, hmod, hdet⟩

end Erdos3.VectorPolynomial

end

end OAI
