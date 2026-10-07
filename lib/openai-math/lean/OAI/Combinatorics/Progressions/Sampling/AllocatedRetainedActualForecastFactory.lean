import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

variable (z : A.Path) (centerLift : ∀ j, U j)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (hrecovered : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm
      centerLift z.1.val z.2.val sample f)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride : ℝ)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) (depth : ℕ → ℕ)
    (hgood : letI := actualForecastPrimeNeZero primes hprime
      (∏ p ∈ primes, p ^ largestTestedBadDepth depth
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p f) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    (hdet : ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)

noncomputable def allocatedRecoveredGoodForecastPath :
    ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value N τ 1 (preparedCenteredForecastSpatialLog Pdim)
      (2 * Fintype.card X * Qstride +
        (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11) 0 := by
  let commonTuple : G → IntegerScalarCubeBox Empty S.value :=
    fun _ _ => ⟨0, Finset.mem_Ico.mpr ⟨by omega, by exact_mod_cast S.positive⟩⟩
  have hnoise : z.2.val ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1 := by
    simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq]
      using z.2.property
  exact preparedCenteredGoodActualForecastPath B U b S hR hσ hb o poly hm
    Dmod spatial kernel block e N τ ξ 1 Pdim
    ((Pdim + preparedCenteredForecastThresholdExponent) ^ preparedCenteredForecastThresholdExponent)
    0 gainLog Qstride z.1.val z.2.val centerLift sample f hrecovered
    commonTuple primes hprime depth (fun _ => 0) (fun _ _ => 0) stride hgood (by simp)
    (fun _ _ => 0) (fun _ _ => 1) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ => by norm_num) hPdim hX hvars A.trim_pos A.narrow_pos A.size_pos
    hnoise hnX hgainLog hstride
    (preparedCenteredForecast_threshold_inverse hPdim hnX hX hgainLog hgainDim)
    (by simpa only [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_eq] using hdet)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in

theorem allocatedRecoveredGoodForecastPath_data :
    let path := allocatedRecoveredGoodForecastPath z centerLift sample f hrecovered Dmod spatial kernel block e Pdim gainLog Qstride
      primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet
    path.center = centerLift ∧ path.base = z.1.val ∧ path.noise = z.2.val ∧
      path.sample = sample ∧ path.read = allocatedReplaceReadNoise B z.2.val f ∧
      path.primes = primes ∧ path.exponent = depth ∧ path.prescribed = (fun _ => 0) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {Selected : Type}
    {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad)

noncomputable def allocatedRecoveredGoodForecastPathForSetup :
    ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ Dmod spatial kernel block
      (spatialTwoBlockEquiv e) (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      S.value N τ 1 setup.P setup.Pbad 0 :=
  (allocatedRecoveredGoodForecastPath z centerLift sample f hrecovered Dmod spatial kernel block e Pdim gainLog Qstride
    primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet).enlargeBudgets
    hPmodel hPbad le_rfl

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in

theorem allocatedRecoveredGoodForecastPathForSetup_data :
    let path := allocatedRecoveredGoodForecastPathForSetup z centerLift sample f hrecovered Dmod spatial kernel block e Pdim gainLog Qstride
      primes hprime depth hgood hPdim hX hvars hnX hgainLog hgainDim hstride hdet
      setup hPmodel hPbad
    path.center = centerLift ∧ path.base = z.1.val ∧ path.noise = z.2.val ∧
      path.sample = sample ∧ path.read = allocatedReplaceReadNoise B z.2.val f ∧
      path.primes = primes ∧ path.exponent = depth ∧ path.prescribed = (fun _ => 0) ∧
      path.origin = (fun _ _ => 0) ∧ path.lower = (fun _ _ => 0) ∧ path.width = (fun _ _ => 1) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j ex, coefficients (poly j) ex ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

def AllocatedRetainedActualForecastFactoryConclusion
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (centerLift : ∀ j, U j)
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (retained : Finset A.Path)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Ptest Crecovered : ℝ)
    {Selected : Type} {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice) : Prop :=
    ∃ path : retained → ActualFixedSpatialForecastPath (Eout := E) B U b S hR hσ
      Dmod spatial kernel block (spatialTwoBlockEquiv e)
      (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) N τ 1 setup.P setup.Pbad 0,
      (∀ z, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ poly hm
        (allocatedShortAxis (I := I) U b S.value) spatial kernel block Crecovered
        center (path z).center (path z).base (sampleFn z.val.1.val) (readFn z.val.1.val)) ∧
      (∀ z, (path z).primes = boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊) ∧
      (∀ z, (path z).exponent = fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊) ∧
      (∀ z, (path z).base = z.val.1.val) ∧
      (∀ z, (path z).noise = z.val.2.val) ∧
      (∀ z, (path z).sample = sampleFn z.val.1.val z.val.2.val) ∧
      (∀ z, (path z).read = allocatedReplaceReadNoise B z.val.2.val
        (allocatedJointFrameRead z.val.1.val (readFn z.val.1.val z.val.2.val))) ∧
      (∀ z, (path z).center = centerLift)

theorem exists_allocatedRetainedActualForecastFactory
    (bW : ∀ j, Basis (E j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (centerLift : ∀ j, U j)
    (sampleFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (readFn : (X → ℤ) → (Option (LayerSamplerVariables G I n B) × X → ℤ) →
      AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (productive retained : Finset A.Path) (hsub : retained ⊆ productive)
    (Dmod : ℕ) {Lrank : ℕ} (spatial : Fin Lrank ↪ G)
    (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
      (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
    (e : Fin 2 × X ↪ G) (Pdim gainLog Qstride Ptest Crecovered : ℝ)
    (hglobal : ∀ base, AllocatedCenteredRecoveredSampleReadAt B U bW b hb o S hR hσ
      poly hm (allocatedShortAxis (I := I) U b S.value) spatial kernel block Crecovered
      center centerLift base (sampleFn base) (readFn base))
    (hrecovered : ∀ z ∈ productive, AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ
      poly hm centerLift z.1.val z.2.val (sampleFn z.1.val z.2.val)
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val)))
    (hgood : let primes := boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊
      letI := actualForecastPrimeNeZero primes (boundedPrimes_prime _)
      ∀ z ∈ productive,
      (∏ p ∈ primes, p ^ largestTestedBadDepth (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊)
        (allocatedActualPrimeBad (allocatedShortAxis (I := I) U b S.value)
          spatial kernel block primes (modularForecastRankConstant m Dmod : ℝ)) p
        (allocatedJointFrameRead z.1.val (readFn z.1.val z.2.val))) ≤
      (∏ x, stride x) ^ 2 * (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) *
        quantitativeBadPrimeRadius (gainLog + 8)))
    (hdet : ∀ z ∈ productive, ∀ t : Fin 2,
      spatialMatrixBlockThreshold (Fintype.card X) (jointSpatialError gainLog) / 2 <
        |Matrix.det (fun i j : X => spatialMatrixNormalizedEntries e A.widths z.2.val (t,j,i))|)
    (hPdim : 0 ≤ Pdim) (hX : (Fintype.card X : ℝ) ≤ Pdim)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ Pdim)
    (hnX : 0 < Fintype.card X) (hgainLog : 0 ≤ gainLog) (hgainDim : gainLog ≤ Pdim)
    (hstride : ∀ x, (stride x : ℝ) ≤ Real.exp Qstride)
    {Selected : Type} {selected : Selected → Σ j : Fin m, Fin (n j)} {δslice : ℝ}
    (setup : ActualFixedSpatialForecastSetup (X := X) (Eout := E)
      B U b S Dmod selected τ δslice)
    (hPmodel : preparedCenteredForecastSpatialLog Pdim ≤ setup.P)
    (hPbad : 2 * Fintype.card X * Qstride +
      (smallPrimePowerCorrection (modularCoefficientPrimeThreshold m) : ℝ) + gainLog + 11 ≤ setup.Pbad) :
    AllocatedRetainedActualForecastFactoryConclusion bW centerLift sampleFn readFn retained
      Dmod spatial kernel block e Ptest Crecovered setup := by
  let path := fun z : retained => allocatedRecoveredGoodForecastPathForSetup
    (A := A) z.val centerLift (sampleFn z.val.1.val z.val.2.val)
    (allocatedJointFrameRead z.val.1.val (readFn z.val.1.val z.val.2.val))
    (hrecovered z.val (hsub z.property)) Dmod spatial kernel block e Pdim gainLog Qstride
    (boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊) (boundedPrimes_prime _)
    (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊) (hgood z.val (hsub z.property))
    hPdim hX hvars hnX hgainLog hgainDim hstride (hdet z.val (hsub z.property))
    setup hPmodel hPbad
  have hdata (z : retained) := allocatedRecoveredGoodForecastPathForSetup_data
    (A := A) z.val centerLift (sampleFn z.val.1.val z.val.2.val)
    (allocatedJointFrameRead z.val.1.val (readFn z.val.1.val z.val.2.val))
    (hrecovered z.val (hsub z.property)) Dmod spatial kernel block e Pdim gainLog Qstride
    (boundedPrimes ⌈Real.exp (2 * Ptest)⌉₊) (boundedPrimes_prime _)
    (fun p => Nat.log p ⌈Real.exp (2 * Ptest)⌉₊) (hgood z.val (hsub z.property))
    hPdim hX hvars hnX hgainLog hgainDim hstride (hdet z.val (hsub z.property))
    setup hPmodel hPbad
  refine ⟨path, ?_, (fun z => (hdata z).2.2.2.2.2.1),
    (fun z => (hdata z).2.2.2.2.2.2.1), (fun z => (hdata z).2.1),
    (fun z => (hdata z).2.2.1), (fun z => (hdata z).2.2.2.1),
    (fun z => (hdata z).2.2.2.2.1), (fun z => (hdata z).1)⟩
  intro z
  rw [(hdata z).1, (hdata z).2.1]
  exact hglobal z.val.1.val

end Erdos3.VectorPolynomial

end

end OAI
