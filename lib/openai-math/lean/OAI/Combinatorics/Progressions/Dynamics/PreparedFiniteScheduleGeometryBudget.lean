import OAI.Combinatorics.Progressions.Estimates.InitializedEarlyCanonicalSliceScales
import OAI.Combinatorics.Progressions.Estimates.PreparedFiniteNestedSourceRelativeInitializerBounds
import OAI.Combinatorics.Progressions.Polynomial.PreparedUniformDegreeTolerance

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedFiniteSchedulePowerBudget (m nStages : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type*} [Fintype K] {P D pRadius Qσ Pmin Qw : ℝ}
      {pDetect Ptail Prho Pk target Tmod : K → ℝ},
      Fintype.card K ≤ nStages → 0 ≤ P → D ∈ Set.Icc 0 P → pRadius ∈ Set.Icc 0 P →
      Qσ ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P → Qw ∈ Set.Icc 0 P →
      (∀ s, pDetect s ∈ Set.Icc 0 P) →
      (∀ s, Ptail s ∈ Set.Icc 0 P) → (∀ s, Prho s ∈ Set.Icc 0 P) →
      (∀ s, Pk s ∈ Set.Icc 0 P) → (∀ s, target s ∈ Set.Icc 0 P) →
      (∀ s, Tmod s ∈ Set.Icc 0 P) →
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      Pscale ∈ Set.Icc 0 ((P + C) ^ C) ∧
        (∑ s, lengthLogs s) ∈ Set.Icc 0 ((P + C) ^ C) ∧
        Pseed ∈ Set.Icc 0 ((P + C) ^ C) ∧
        allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 ((P + C) ^ C) := by
  obtain ⟨A, _, hA⟩ := exists_allocatedAffineScaleLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let pScale := Polynomial.C (nStages + 3) * X
  let pLength := (Polynomial.C (nStages + 9) * X + 2 + Polynomial.C A) ^ A
  let pInput := pScale + Polynomial.C nStages * pLength + X + 1
  let pSeed := (1 + pInput ^ 2) * (5 * pInput + 49)
  let pWitness := (1 + pSeed ^ 2) * (5 * pSeed + 49) + pSeed ^ 2 * X
  let poly := pScale + pSeed + pWitness
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ P D pRadius Qσ Pmin Qw pDetect Ptail Prho Pk target Tmod
    hCard hP hD hRadius hQσ hPmin hQw hDetect hTail hRho hPk hTarget hMod
    Pscale lengthLogs Pseed
  let scaleBound := ((nStages + 3 : ℕ) : ℝ) * P
  let lengthBound := (((nStages + 9 : ℕ) : ℝ) * P + 2 + A) ^ A
  let inputBound := scaleBound + (nStages : ℝ) * lengthBound + P + 1
  let seedBound := allocatedScaleLog inputBound
  let witnessBound := allocatedWitnessScaleLog seedBound P
  have hTailSum : (∑ s, Ptail s) ≤ (nStages : ℝ) * P := by
    calc
      _ ≤ ∑ _s : K, P := Finset.sum_le_sum (fun s _ => (hTail s).2)
      _ = (Fintype.card K : ℝ) * P := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hP
  have hTailSum0 : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => (hTail s).1)
  have hScale0 : 0 ≤ Pscale := add_nonneg (add_nonneg (add_nonneg hD.1 hRadius.1) hTailSum0) hQσ.1
  have hScale : Pscale ≤ scaleBound := by
    calc
      _ ≤ P + P + (nStages : ℝ) * P + P :=
        add_le_add (add_le_add (add_le_add hD.2 hRadius.2) hTailSum) hQσ.2
      _ = _ := by dsimp only [scaleBound]; push_cast; ring
  have hF (s : K) : 0 ≤ pDetect s + 2 := by linarith only [(hDetect s).1]
  have hLogs0 (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD.1 hScale0 (hRho s).1 (hPk s).1
      (hTarget s).1 (hF s) (hMod s).1).2.2.1
  have hLengths (s) : lengthLogs s ≤ lengthBound := by
    have hInput0 : 0 ≤ D + Pscale + lengthLogs s + 1 := by
      linarith only [hD.1, hScale0, hLogs0 s]
    have hLengthInput : lengthLogs s ≤ D + Pscale + lengthLogs s + 1 := by
      linarith only [hD.1, hScale0]
    apply (hLengthInput.trans (le_allocatedScaleLog hInput0)).trans
    apply (hA D Pscale (Prho s) (Pk s) (target s) (pDetect s + 2) (Tmod s)
      hD.1 hScale0 (hRho s).1 (hPk s).1 (hTarget s).1 (hF s) (hMod s).1).trans
    apply pow_le_pow_left₀ (by
      have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
      linarith only [hD.1, hScale0, (hRho s).1, (hPk s).1, (hTarget s).1,
        hF s, (hMod s).1, hA0])
    calc
      _ ≤ P + scaleBound + P + P + P + (P + 2) + P + A := by
        linarith only [hD.2, hScale, (hRho s).2, (hPk s).2,
          (hTarget s).2, (hDetect s).2, (hMod s).2]
      _ = _ := by dsimp only [scaleBound]; push_cast; ring
  have hLengthSum0 : 0 ≤ ∑ s, lengthLogs s := Finset.sum_nonneg (fun s _ => hLogs0 s)
  have hLengthBound0 : 0 ≤ lengthBound := by dsimp only [lengthBound]; positivity
  have hLengthSum : (∑ s, lengthLogs s) ≤ (nStages : ℝ) * lengthBound := by
    calc
      _ ≤ ∑ _s : K, lengthBound := Finset.sum_le_sum (fun s _ => hLengths s)
      _ = (Fintype.card K : ℝ) * lengthBound := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hCard) hLengthBound0
  have hInput0 : 0 ≤ Pscale + ∑ s, lengthLogs s + Pmin + 1 := by
    linarith only [hScale0, hLengthSum0, hPmin.1]
  have hInput : Pscale + ∑ s, lengthLogs s + Pmin + 1 ≤ inputBound := by
    dsimp only [inputBound]
    linarith only [hScale, hLengthSum, hPmin.2]
  have hSeed0 : 0 ≤ Pseed := allocatedScaleLog_nonneg hInput0
  have hSeed : Pseed ≤ seedBound := by
    dsimp only [Pseed, seedBound, allocatedScaleLog]
    gcongr
  have hWitness0 : 0 ≤ allocatedWitnessScaleLog Pseed Qw :=
    add_nonneg (allocatedScaleLog_nonneg hSeed0) (mul_nonneg (sq_nonneg _) hQw.1)
  have hWitness : allocatedWitnessScaleLog Pseed Qw ≤ witnessBound := by
    have hs : allocatedScaleLog Pseed ≤ allocatedScaleLog seedBound := by
      unfold allocatedScaleLog
      gcongr
    exact add_le_add hs (mul_le_mul (pow_le_pow_left₀ hSeed0 hSeed 2)
      hQw.2 hQw.1 (sq_nonneg _))
  have hScaleBound0 : 0 ≤ scaleBound := mul_nonneg (Nat.cast_nonneg _) hP
  have hInputBound0 : 0 ≤ inputBound := by dsimp only [inputBound]; positivity
  have hSeedBound0 : 0 ≤ seedBound := allocatedScaleLog_nonneg hInputBound0
  have hWitnessBound0 : 0 ≤ witnessBound :=
    add_nonneg (allocatedScaleLog_nonneg hSeedBound0) (mul_nonneg (sq_nonneg _) hP)
  have hEnvelope : scaleBound + seedBound + witnessBound ≤ (P + C) ^ C := by
    simpa [poly, pScale, pLength, pInput, pSeed, pWitness, X, scaleBound, lengthBound,
      inputBound, seedBound, witnessBound, allocatedScaleLog, allocatedWitnessScaleLog,
      Polynomial.eval₂_pow] using hpoly P hP
  have hSumSeed : (∑ s, lengthLogs s) ≤ seedBound := by
    apply le_trans (b := inputBound) _ (le_allocatedScaleLog hInputBound0)
    dsimp only [inputBound]
    linarith only [hLengthSum, hScaleBound0, hP]
  exact ⟨⟨hScale0, by linarith only [hScale, hEnvelope, hSeedBound0, hWitnessBound0]⟩,
    ⟨hLengthSum0, by linarith only [hSumSeed, hEnvelope, hScaleBound0, hWitnessBound0]⟩,
    ⟨hSeed0, by linarith only [hSeed, hEnvelope, hScaleBound0, hWitnessBound0]⟩,
    ⟨hWitness0, by linarith only [hWitness, hEnvelope, hScaleBound0, hSeedBound0]⟩⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped NNReal

private theorem canonical_minorVariable_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorVariableEnvelope D ≤ affineMinorVariableEnvelope D' := by
  have hD'0 := hD0.trans hD
  dsimp only [affineMinorVariableEnvelope]
  gcongr

private theorem canonical_minorDegree_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorDegreeEnvelope D ≤ affineMinorDegreeEnvelope D' := by
  have hD'0 := hD0.trans hD
  dsimp only [affineMinorDegreeEnvelope]
  gcongr

private theorem canonical_minorConstant_mono {D D' : ℝ} (hD0 : 0 ≤ D) (hD : D ≤ D') :
    affineMinorConstantEnvelope D ≤ affineMinorConstantEnvelope D' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hd := canonical_minorDegree_mono hD0 hD
  have hd0 := affineMinorDegreeEnvelope_nonneg hD0
  have hd'0 := affineMinorDegreeEnvelope_nonneg hD'0
  dsimp only [affineMinorConstantEnvelope]
  gcongr

private theorem canonical_minorLog_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineMinorLogEnvelope D P E F ≤ affineMinorLogEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hd := canonical_minorDegree_mono hD0 hD
  have hc := canonical_minorConstant_mono hD0 hD
  have hv0 := affineMinorVariableEnvelope_nonneg hD0
  have hv'0 := affineMinorVariableEnvelope_nonneg hD'0
  have hd0 := affineMinorDegreeEnvelope_nonneg hD0
  have hd'0 := affineMinorDegreeEnvelope_nonneg hD'0
  have hc0 := affineMinorConstantEnvelope_nonneg hD0
  dsimp only [affineMinorLogEnvelope]
  gcongr

private theorem canonical_inverseAxis_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineInverseAxisEnvelope D P E F ≤ affineInverseAxisEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hm := canonical_minorLog_mono hD0 hP0 hE0 hF0 hD hP hE hF
  dsimp only [affineInverseAxisEnvelope]
  gcongr

private theorem canonical_derivativeAxis_mono {D D' P P' : ℝ}
    (hD0 : 0 ≤ D) (hD : D ≤ D') (hP : P ≤ P') :
    affineDerivativeAxisEnvelope D P ≤ affineDerivativeAxisEnvelope D' P' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  dsimp only [affineDerivativeAxisEnvelope]
  gcongr

private theorem canonical_weightAxis_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    affineWeightAxisEnvelope D P E F ≤ affineWeightAxisEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hm := canonical_minorLog_mono hD0 hP0 hE0 hF0 hD hP hE hF
  dsimp only [affineWeightAxisEnvelope]
  gcongr

private theorem canonical_jointSource_mono {D D' P P' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hP0 : 0 ≤ P) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    jointAffineSourceEnvelope D P E F ≤ jointAffineSourceEnvelope D' P' E' F' := by
  have hD'0 := hD0.trans hD
  have hv := canonical_minorVariable_mono hD0 hD
  have hi := canonical_inverseAxis_mono hD0 hP0 hE0 hF0 hD hP hE hF
  have hd := canonical_derivativeAxis_mono hD0 hD hP
  have hw := canonical_weightAxis_mono hD0 hP0 hE0 hF0 hD hP hE hF
  have hv0 := affineMinorVariableEnvelope_nonneg hD0
  have hi0 := affineInverseAxisEnvelope_nonneg hD0 hP0 hE0 hF0
  have hd0 := affineDerivativeAxisEnvelope_nonneg hD0 hP0
  have hw0 := affineWeightAxisEnvelope_nonneg hD0 hP0 hE0 hF0
  dsimp only [jointAffineSourceEnvelope, jointAffineInverseEnvelope,
    jointAffineDerivativeEnvelope, jointAffineWeightEnvelope]
  gcongr

private theorem canonical_profileInput_mono {D D' A A' T T' E E' F F' : ℝ}
    (hD0 : 0 ≤ D) (hA0 : 0 ≤ A) (hT0 : 0 ≤ T) (hE0 : 0 ≤ E) (hF0 : 0 ≤ F)
    (hD : D ≤ D') (hA : A ≤ A') (hT : T ≤ T') (hE : E ≤ E') (hF : F ≤ F') :
    affineProfileInputEnvelope D A T E F ≤ affineProfileInputEnvelope D' A' T' E' F' := by
  have hD'0 := hD0.trans hD
  apply canonical_jointSource_mono hD0
    (by dsimp only [affineProfileCoefficientEnvelope]; positivity) (by positivity) hF0 hD
  · dsimp only [affineProfileCoefficientEnvelope]; gcongr
  · gcongr
  · exact hF

theorem exists_canonicalSliceEarlyScale_budget (m s Cdetect : ℕ) (A T : ℝ≥0) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type*} [Fintype G] {count nX : ℕ}
      {P D p q a target Qstride pRadius : ℝ},
      0 ≤ P → D ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → q ∈ Set.Icc 0 P →
      a ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      pRadius ∈ Set.Icc 0 P → (count : ℝ) ≤ P → (nX : ℝ) ≤ P →
      (Fintype.card G : ℝ) ≤ P →
      let gainLog := slicedDetectionGainLog s Cdetect count p q a
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
      let F := p + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (A : ℝ) (T : ℝ) E F
      let Pscale := pRadius + Ptail
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
      let budget := (P + C) ^ C
      P ≤ budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
      Tmod ∈ Set.Icc 0 budget ∧ Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget := by
  obtain ⟨Adet, _, hdet⟩ := exists_slicedDetection_uniform_budget s Cdetect
  let Ac : ℕ := ⌈(A : ℝ)⌉₊
  let Tc : ℕ := ⌈(T : ℝ)⌉₊
  let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
  let X : Polynomial ℕ := Polynomial.X
  let detPoly := (4 * X + Polynomial.C Adet) ^ Adet
  let errorPoly := X + X * (Polynomial.C (m * 2 ^ (m + 1)) * detPoly) + 5
  let inputPoly := affineProfileInputEnvelope X (Polynomial.C Ac) (Polynomial.C Tc) errorPoly (X + 2)
  let rhoPoly := 2 * inputPoly + 2
  let tailPoly := affineProfileToleranceEnvelope m X (X * (X + 1) + X * X + X + 1)
    (Polynomial.C Ac) (Polynomial.C Tc) errorPoly (X + 2)
  let modPoly := Polynomial.C (m + 1) * detPoly + X * X
  let scalePoly := (X + (X + tailPoly) + rhoPoly + detPoly + X + (X + 2) + modPoly + Polynomial.C K) ^ K
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (X + detPoly + rhoPoly + tailPoly + modPoly + (X + tailPoly) + scalePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P D p q a target Qstride pRadius hP hD hp hq ha ht hQs hRadius hc hnX hG
    gainLog Pk F Tmod E Prho Ptail Pscale K' scaleLog budget
  let detBound := (4 * P + Adet) ^ Adet
  let errorBound := P + P * ((m * 2 ^ (m + 1) : ℕ) * detBound) + 5
  let inputBound := affineProfileInputEnvelope P (Ac : ℝ) (Tc : ℝ) errorBound (P + 2)
  let rhoBound := 2 * inputBound + 2
  let tailBound := affineProfileToleranceEnvelope m P (P * (P + 1) + P * P + P + 1)
    (Ac : ℝ) (Tc : ℝ) errorBound (P + 2)
  let modBound := ((m + 1 : ℕ) : ℝ) * detBound + P * P
  let scaleBound := (P + (P + tailBound) + rhoBound + detBound + P + (P + 2) + modBound + K) ^ K
  have hD0 := hD.1
  have hp0 := hp.1
  have hq0 := hq.1
  have ha0 := ha.1
  have ht0 := ht.1
  have hQs0 := hQs.1
  have hRadius0 := hRadius.1
  have hgain0 : 0 ≤ gainLog := slicedDetectionGainLog_nonneg s Cdetect count hp0 hq0 ha0
  have hk0 : 0 ≤ Pk := by dsimp only [Pk]; rw [scalarKernelLogarithmicBudget_eq]; positivity
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hE0 : 0 ≤ E := by dsimp only [E]; positivity
  have hinput0 : 0 ≤ affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F :=
    jointAffineSourceEnvelope_nonneg hD0
      (by dsimp [affineProfileCoefficientEnvelope]; positivity) (by positivity) hF0
  have hrho0 : 0 ≤ Prho := by dsimp only [Prho]; positivity
  have htail0 : 0 ≤ Ptail := by dsimp only [Ptail, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]; positivity
  have hmod0 : 0 ≤ Tmod := by dsimp only [Tmod]; positivity
  have hscaleP0 : 0 ≤ Pscale := add_nonneg hRadius0 htail0
  have hscale0 : 0 ≤ scaleLog := by dsimp only [scaleLog]; positivity
  have hdet := hdet (G := G) hP hp0 hq0 ha0 hc hG
  have hdetPow : (P + p + q + a + Adet) ^ Adet ≤ detBound := by
    apply pow_le_pow_left₀ (by positivity)
    linarith only [hp.2, hq.2, ha.2]
  have hgain : gainLog ≤ detBound := hdet.1.trans hdetPow
  have hk : Pk ≤ detBound := hdet.2.trans hdetPow
  have hAc : (A : ℝ) ≤ Ac := Nat.le_ceil _
  have hTc : (T : ℝ) ≤ Tc := Nat.le_ceil _
  have hdet0 : 0 ≤ detBound := by dsimp only [detBound]; positivity
  have herror0 : 0 ≤ errorBound := by dsimp only [errorBound]; positivity
  have hinputBound0 : 0 ≤ inputBound := jointAffineSourceEnvelope_nonneg hP
    (by dsimp [affineProfileCoefficientEnvelope]; positivity) (by positivity) (by positivity)
  have hrhoBound0 : 0 ≤ rhoBound := by dsimp only [rhoBound]; positivity
  have htailBound0 : 0 ≤ tailBound := by dsimp only [tailBound, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]; positivity
  have hmodBound0 : 0 ≤ modBound := by dsimp only [modBound]; positivity
  have hscaleBound0 : 0 ≤ scaleBound := by dsimp only [scaleBound]; positivity
  have hE : E ≤ errorBound := by dsimp only [E, errorBound]; gcongr; exact ht.2; exact hD.2
  have hF : F ≤ P + 2 := by dsimp only [F]; linarith only [hp.2]
  have hinput : affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F ≤ inputBound :=
    canonical_profileInput_mono hD0 A.coe_nonneg T.coe_nonneg hE0 hF0 hD.2 hAc hTc hE hF
  have hrho : Prho ≤ rhoBound := by dsimp only [Prho, rhoBound]; gcongr
  have htail : Ptail ≤ tailBound := by
    dsimp only [Ptail, tailBound, affineProfileToleranceEnvelope, affineProfileCoefficientEnvelope]
    gcongr
    all_goals first | exact hinput | exact hD.2
  have hmod : Tmod ≤ modBound := by dsimp only [Tmod, modBound]; gcongr; exact hQs.2
  have hscaleP : Pscale ≤ P + tailBound := add_le_add hRadius.2 htail
  have hscale : scaleLog ≤ scaleBound := by
    dsimp only [scaleLog, scaleBound]
    apply pow_le_pow_left₀ (by positivity)
    gcongr
    all_goals first | exact hD.2 | exact ht.2
  have hsum : P + detBound + rhoBound + tailBound + modBound + (P + tailBound) + scaleBound ≤ budget := by
    simpa [X, detPoly, errorPoly, inputPoly, rhoPoly, tailPoly, modPoly, scalePoly,
      detBound, errorBound, inputBound, rhoBound, tailBound, modBound, scaleBound,
      affineProfileInputEnvelope, affineProfileCoefficientEnvelope, affineProfileToleranceEnvelope,
      jointAffineSourceEnvelope, jointAffineInverseEnvelope, jointAffineDerivativeEnvelope,
      jointAffineWeightEnvelope, affineInverseAxisEnvelope, affineDerivativeAxisEnvelope,
      affineWeightAxisEnvelope, affineMinorLogEnvelope, affineMinorVariableEnvelope,
      affineMinorDegreeEnvelope, affineMinorConstantEnvelope, Polynomial.eval₂_pow] using hbound P hP
  refine ⟨?_, ⟨hgain0, ?_⟩, ⟨hk0, ?_⟩, ⟨hrho0, ?_⟩, ⟨htail0, ?_⟩,
    ⟨hmod0, ?_⟩, ⟨hscaleP0, ?_⟩, ⟨hscale0, ?_⟩⟩ <;>
    linarith only [hsum, hP, hgain, hk, hrho, htail, hmod, hscaleP, hscale,
      hdet0, hrhoBound0, htailBound0, hmodBound0, hscaleBound0]

theorem exists_primitiveCanonicalSliceEarlyScale_budget (m s Cdetect : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type*} [Fintype G] {count nX : ℕ}
      {P pnum p q a target Qstride pRadius : ℝ},
      0 ≤ P → pnum ∈ Set.Icc 0 P → p ∈ Set.Icc 0 P → q ∈ Set.Icc 0 P →
      a ∈ Set.Icc 0 P → target ∈ Set.Icc 0 P → Qstride ∈ Set.Icc 0 P →
      pRadius ∈ Set.Icc 0 P → (count : ℝ) ≤ P → (nX : ℝ) ≤ P →
      (Fintype.card G : ℝ) ≤ P →
      let D := allocatedComparisonDimension m pnum
      let gainLog := slicedDetectionGainLog s Cdetect count p q a
      let Pk := scalarKernelLogarithmicBudget (Fin (s + 1)) G (gainLog + p + 4)
      let F := p + 2
      let Tmod := ((m + 1 : ℕ) : ℝ) * Pk + nX * Qstride
      let E := target + D * ((m * 2 ^ (m + 1) : ℕ) * Pk) + 5
      let Prho := 2 * affineProfileInputEnvelope D (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F + 2
      let Ptail := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) E F
      let Pscale := pRadius + Ptail
      let K := Classical.choose (exists_allocatedAffineScaleLog_bound m)
      let scaleLog := (D + Pscale + Prho + Pk + target + F + Tmod + K) ^ K
      let budget := (P + C) ^ C
      P ≤ budget ∧ D ∈ Set.Icc 0 budget ∧ gainLog ∈ Set.Icc 0 budget ∧ Pk ∈ Set.Icc 0 budget ∧
      Prho ∈ Set.Icc 0 budget ∧ Ptail ∈ Set.Icc 0 budget ∧
      Tmod ∈ Set.Icc 0 budget ∧ Pscale ∈ Set.Icc 0 budget ∧ scaleLog ∈ Set.Icc 0 budget := by
  obtain ⟨Aearly, _, hearly⟩ := exists_canonicalSliceEarlyScale_budget m s Cdetect
    canonicalSublevelCutoffLip canonicalTransitionLip
  let X : Polynomial ℕ := Polynomial.X
  let poly := (allocatedComparisonDimension m X + Polynomial.C Aearly) ^ Aearly
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pnum p q a target Qstride pRadius hP hnum hp hq ha ht hQs hRadius hc hnX hG
    D gainLog Pk F Tmod E Prho Ptail Pscale K scaleLog budget
  let R := allocatedComparisonDimension m P
  have hR0 : 0 ≤ R := (allocatedComparisonDimension_bounds m hP).1
  have hPR : P ≤ R := (allocatedComparisonDimension_bounds m hP).2.2.1
  have hnum0 := hnum.1
  have hD0 : 0 ≤ D := (allocatedComparisonDimension_bounds m hnum0).1
  have hDR : D ≤ R := by
    dsimp only [D, R, allocatedComparisonDimension]
    gcongr <;> exact hnum.2
  have hlift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 R :=
    ⟨hx.1, hx.2.trans hPR⟩
  have hbudget : (R + Aearly) ^ Aearly ≤ budget := by
    simpa [poly, X, R, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound P hP
  obtain ⟨hbase, hgain, hk, hrho, htail, hmod, hscaleP, hscale⟩ :=
    hearly (G := G) hR0 ⟨hD0, hDR⟩ (hlift hp) (hlift hq) (hlift ha) (hlift ht)
      (hlift hQs) (hlift hRadius) (hc.trans hPR) (hnX.trans hPR) (hG.trans hPR)
  have hbudgetLift {x : ℝ} (hx : x ∈ Set.Icc 0 ((R + Aearly) ^ Aearly)) :
      x ∈ Set.Icc 0 budget := ⟨hx.1, hx.2.trans hbudget⟩
  exact ⟨hPR.trans (hbase.trans hbudget), ⟨hD0, hDR.trans (hbase.trans hbudget)⟩,
    hbudgetLift hgain, hbudgetLift hk, hbudgetLift hrho, hbudgetLift htail,
    hbudgetLift hmod, hbudgetLift hscaleP, hbudgetLift hscale⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleEarlyBudget
    (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
      {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Qstride : ℝ}
      (pDetect aDetect target : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      (∀ k, pDetect k ∈ Set.Icc 0 P) → (∀ k, aDetect k ∈ Set.Icc 0 P) →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : K =>
        slicedDetectionGainLog (degree s) (Cdetect s) count (pDetect s) (pDetect s) (aDetect s)
      let Pk := fun s : K =>
        scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
      let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : K => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
      let Ptail := fun s : K => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Index := Fin (m + 1) × Fin (Cmax + 1)
  let Cs := fun i : Index => Classical.choose
    (exists_primitiveCanonicalSliceEarlyScale_budget m i.1.val i.2.val)
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Index, (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ degree Cdetect G _ count nX P Bstruct pnum Qstride pDetect aDetect target
    _hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Index => (P + Cs s) ^ Cs s
  have hpiece (s) : 0 ≤ piece s := by dsimp only [piece]; positivity
  have hradiusBound : 0 ≤ (2 * P + A) ^ A := by positivity
  have hsum0 : 0 ≤ ∑ s, piece s := Finset.sum_nonneg (fun s _ => hpiece s)
  have htotal : P + (2 * P + A) ^ A + ∑ s, piece s ≤ budget := by
    simpa [poly, X, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbound P hP
  have hbase : P ≤ budget := by linarith only [htotal, hradiusBound, hsum0]
  have hradiusCap : (2 * P + A) ^ A ≤ budget := by linarith only [htotal, hP, hsum0]
  have hpieceCap (s) : piece s ≤ budget := by
    have hi : piece s ≤ ∑ i, piece i :=
      Finset.single_le_sum (fun i _ => hpiece i) (Finset.mem_univ s)
    linarith only [htotal, hi, hP, hradiusBound]
  have hradius : pRadius ∈ Set.Icc 0 budget := by
    refine ⟨(allocatedCommonProductRadius_bounds m hB.1 hB.1).1, ?_⟩
    apply (hRadius hB.1 hB.1).trans
    apply le_trans _ hradiusCap
    exact pow_le_pow_left₀ (by linarith only [hB.1, (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]) (by linarith only [hB.2]) A
  let index : K → Index := fun s =>
    (⟨degree s, Nat.lt_succ_of_le (hdegree s)⟩,
      ⟨Cdetect s, Nat.lt_succ_of_le (hCdetect s)⟩)
  have hdata (s : K) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget
        m (degree s) (Cdetect s))).2
        (G := G) hP hnum (hp s) (hp s) (ha s) (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece (index s))) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap (index s))⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨_, hD, _⟩ :=
    (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m 0 0)).2
      (G := G) hP hnum hzero hzero hzero hzero hQ hzero hcount hnX hG
  have hDCap : D ∈ Set.Icc 0 budget :=
    ⟨hD.1, hD.2.trans (hpieceCap (⟨0, Nat.succ_pos m⟩, ⟨0, Nat.succ_pos Cmax⟩))⟩
  exact ⟨hbase, hradius, hDCap, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleEarlyBudgetWithCutoff
    (m d nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
      {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Qstride : ℝ}
      (pDetect aDetect target : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ d) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      (∀ k, pDetect k ∈ Set.Icc 0 P) → (∀ k, aDetect k ∈ Set.Icc 0 P) →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : K =>
        slicedDetectionGainLog (degree s) (Cdetect s) count (pDetect s) (pDetect s) (aDetect s)
      let Pk := fun s : K =>
        scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
      let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : K => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
      let Ptail := fun s : K => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Index := Fin (d + 1) × Fin (Cmax + 1)
  let Cs := fun i : Index => Classical.choose
    (exists_primitiveCanonicalSliceEarlyScale_budget m i.1.val i.2.val)
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Index, (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro K _ degree Cdetect G _ count nX P Bstruct pnum Qstride pDetect aDetect target
    _hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Index => (P + Cs s) ^ Cs s
  have hpiece (s) : 0 ≤ piece s := by dsimp only [piece]; positivity
  have hradiusBound : 0 ≤ (2 * P + A) ^ A := by positivity
  have hsum0 : 0 ≤ ∑ s, piece s := Finset.sum_nonneg (fun s _ => hpiece s)
  have htotal : P + (2 * P + A) ^ A + ∑ s, piece s ≤ budget := by
    simpa [poly, X, piece, Polynomial.eval₂_pow, Polynomial.eval₂_finsetSum] using hbound P hP
  have hbase : P ≤ budget := by linarith only [htotal, hradiusBound, hsum0]
  have hradiusCap : (2 * P + A) ^ A ≤ budget := by linarith only [htotal, hP, hsum0]
  have hpieceCap (s) : piece s ≤ budget := by
    have hi : piece s ≤ ∑ i, piece i :=
      Finset.single_le_sum (fun i _ => hpiece i) (Finset.mem_univ s)
    linarith only [htotal, hi, hP, hradiusBound]
  have hradius : pRadius ∈ Set.Icc 0 budget := by
    refine ⟨(allocatedCommonProductRadius_bounds m hB.1 hB.1).1, ?_⟩
    apply (hRadius hB.1 hB.1).trans
    apply le_trans _ hradiusCap
    exact pow_le_pow_left₀ (by linarith only [hB.1, (show (0 : ℝ) ≤ A from Nat.cast_nonneg A)]) (by linarith only [hB.2]) A
  let index : K → Index := fun s =>
    (⟨degree s, Nat.lt_succ_of_le (hdegree s)⟩,
      ⟨Cdetect s, Nat.lt_succ_of_le (hCdetect s)⟩)
  have hdata (s : K) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget
        m (degree s) (Cdetect s))).2
        (G := G) hP hnum (hp s) (hp s) (ha s) (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece (index s))) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap (index s))⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨_, hD, _⟩ :=
    (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m 0 0)).2
      (G := G) hP hnum hzero hzero hzero hzero hQ hzero hcount hnX hG
  have hDCap : D ∈ Set.Icc 0 budget :=
    ⟨hD.1, hD.2.trans (hpieceCap (⟨0, Nat.succ_pos d⟩, ⟨0, Nat.succ_pos Cmax⟩))⟩
  exact ⟨hbase, hradius, hDCap, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedFiniteScheduleGeometryBudget
    (m nStages Cmax : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {K : Type} [Fintype K] (degree Cdetect : K → ℕ)
      {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum Qstride Qσ Pmin Qw : ℝ}
      (pDetect aDetect target : K → ℝ),
      Fintype.card K ≤ nStages → (∀ k, degree k ≤ m) → (∀ k, Cdetect k ≤ Cmax) →
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      (∀ k, pDetect k ∈ Set.Icc 0 P) → (∀ k, aDetect k ∈ Set.Icc 0 P) →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      Qσ ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P → Qw ∈ Set.Icc 0 P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : K =>
        slicedDetectionGainLog (degree s) (Cdetect s) count (pDetect s) (pDetect s) (aDetect s)
      let Pk := fun s : K =>
        scalarKernelLogarithmicBudget (Fin ((degree s) + 1)) G (gainLog s + pDetect s + 4)
      let Tmod := fun s : K => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : K => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : K => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2) + 2
      let Ptail := fun s : K => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect s + 2)
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect s + 2) (Tmod s)
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        (∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget) ∧
        Pscale ∈ Set.Icc 0 budget ∧ (∑ s, lengthLogs s) ∈ Set.Icc 0 budget ∧
        Pseed ∈ Set.Icc 0 budget ∧ allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedFiniteScheduleEarlyBudget m nStages Cmax
  obtain ⟨L, _, hLate⟩ := exists_preparedFiniteSchedulePowerBudget m nStages
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let latePoly := (earlyPoly + Polynomial.C L) ^ L
  obtain ⟨C, hC, hBound⟩ := exists_natPolynomial_eval_budget (earlyPoly + latePoly)
  refine ⟨C, hC, ?_⟩
  intro K _ degree Cdetect G _ count nX P Bstruct pnum Qstride Qσ Pmin Qw pDetect aDetect target
    hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG hQσ hPmin hQw
    pRadius D gainLog Pk Tmod E Prho Ptail Pscale lengthLogs Pseed budget
  let early := (P + A) ^ A
  let late := (early + L) ^ L
  have hEarly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hLate0 : 0 ≤ late := by dsimp only [late]; positivity
  have hSum : early + late ≤ budget := by
    simpa [X, earlyPoly, latePoly, early, late, Polynomial.eval₂_pow] using hBound P hP
  have hEarlyCap : early ≤ budget := by linarith only [hSum, hLate0]
  have hLateCap : late ≤ budget := by linarith only [hSum, hEarly0]
  obtain ⟨hPEarly, hRadius, hD, hDegrees⟩ :=
    hEarly degree Cdetect (G := G) pDetect aDetect target
      hStages hdegree hCdetect hP hB hnum hp ha hQ htarget hcount hnX hG
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 early :=
    ⟨hx.1, hx.2.trans hPEarly⟩
  obtain ⟨hScale, hLengths, hSeed, hWitness⟩ :=
    hLate hStages hEarly0 hD hRadius (lift hQσ) (lift hPmin) (lift hQw) (fun s => lift (hp s))
      (fun s => (hDegrees s).2.2.2.1) (fun s => (hDegrees s).2.2.1)
      (fun s => (hDegrees s).2.1) (fun s => lift (htarget s))
      (fun s => (hDegrees s).2.2.2.2)
  have earlyLift {x : ℝ} (hx : x ∈ Set.Icc 0 early) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hEarlyCap⟩
  have lateLift {x : ℝ} (hx : x ∈ Set.Icc 0 late) : x ∈ Set.Icc 0 budget :=
    ⟨hx.1, hx.2.trans hLateCap⟩
  refine ⟨hPEarly.trans hEarlyCap, earlyLift hRadius, earlyLift hD, ?_,
    lateLift hScale, lateLift hLengths, lateLift hSeed, lateLift hWitness⟩
  intro s
  exact ⟨earlyLift (hDegrees s).1, earlyLift (hDegrees s).2.1,
    earlyLift (hDegrees s).2.2.1, earlyLift (hDegrees s).2.2.2.1,
    earlyLift (hDegrees s).2.2.2.2⟩

end Erdos3.VectorPolynomial

end

end OAI
