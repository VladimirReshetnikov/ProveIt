import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteScheduleGeometryBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

theorem exists_preparedUniformDegreePowerBudget (m : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {P D pRadius Qσ Pmin Qw pDetect : ℝ}
      {Ptail Prho Pk target Tmod : Fin (m + 1) → ℝ},
      0 ≤ P → D ∈ Set.Icc 0 P → pRadius ∈ Set.Icc 0 P →
      Qσ ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P → Qw ∈ Set.Icc 0 P →
      pDetect ∈ Set.Icc 0 P →
      (∀ s, Ptail s ∈ Set.Icc 0 P) → (∀ s, Prho s ∈ Set.Icc 0 P) →
      (∀ s, Pk s ∈ Set.Icc 0 P) → (∀ s, target s ∈ Set.Icc 0 P) →
      (∀ s, Tmod s ∈ Set.Icc 0 P) →
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect + 2) (Tmod s)
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      Pscale ∈ Set.Icc 0 ((P + C) ^ C) ∧
        (∑ s, lengthLogs s) ∈ Set.Icc 0 ((P + C) ^ C) ∧
        Pseed ∈ Set.Icc 0 ((P + C) ^ C) ∧
        allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 ((P + C) ^ C) := by
  obtain ⟨A, _, hA⟩ := exists_allocatedAffineScaleLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let pScale := Polynomial.C (m + 4) * X
  let pLength := (Polynomial.C (m + 10) * X + 2 + Polynomial.C A) ^ A
  let pInput := pScale + Polynomial.C (m + 1) * pLength + X + 1
  let pSeed := (1 + pInput ^ 2) * (5 * pInput + 49)
  let pWitness := (1 + pSeed ^ 2) * (5 * pSeed + 49) + pSeed ^ 2 * X
  let poly := pScale + pSeed + pWitness
  obtain ⟨C, hC, hpoly⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro P D pRadius Qσ Pmin Qw pDetect Ptail Prho Pk target Tmod
    hP hD hRadius hQσ hPmin hQw hDetect hTail hRho hPk hTarget hMod
    Pscale lengthLogs Pseed
  let scaleBound := ((m + 4 : ℕ) : ℝ) * P
  let lengthBound := (((m + 10 : ℕ) : ℝ) * P + 2 + A) ^ A
  let inputBound := scaleBound + ((m + 1 : ℕ) : ℝ) * lengthBound + P + 1
  let seedBound := allocatedScaleLog inputBound
  let witnessBound := allocatedWitnessScaleLog seedBound P
  have hTailSum : (∑ s, Ptail s) ≤ ((m + 1 : ℕ) : ℝ) * P := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin (m + 1)))) =>
        (hTail s).2)
  have hTailSum0 : 0 ≤ ∑ s, Ptail s := Finset.sum_nonneg (fun s _ => (hTail s).1)
  have hScale0 : 0 ≤ Pscale := add_nonneg (add_nonneg (add_nonneg hD.1 hRadius.1) hTailSum0) hQσ.1
  have hScale : Pscale ≤ scaleBound := by
    calc
      _ ≤ P + P + ((m + 1 : ℕ) : ℝ) * P + P :=
        add_le_add (add_le_add (add_le_add hD.2 hRadius.2) hTailSum) hQσ.2
      _ = _ := by dsimp only [scaleBound]; push_cast; ring
  have hF : 0 ≤ pDetect + 2 := by linarith only [hDetect.1]
  have hLogs0 (s) : 0 ≤ lengthLogs s :=
    (allocatedAffineLengthLog_bounds m hD.1 hScale0 (hRho s).1 (hPk s).1
      (hTarget s).1 hF (hMod s).1).2.2.1
  have hLengths (s) : lengthLogs s ≤ lengthBound := by
    have hInput0 : 0 ≤ D + Pscale + lengthLogs s + 1 := by
      linarith only [hD.1, hScale0, hLogs0 s]
    have hLengthInput : lengthLogs s ≤ D + Pscale + lengthLogs s + 1 := by
      linarith only [hD.1, hScale0]
    apply (hLengthInput.trans (le_allocatedScaleLog hInput0)).trans
    apply (hA D Pscale (Prho s) (Pk s) (target s) (pDetect + 2) (Tmod s)
      hD.1 hScale0 (hRho s).1 (hPk s).1 (hTarget s).1 hF (hMod s).1).trans
    apply pow_le_pow_left₀ (by
      have hA0 : 0 ≤ (A : ℝ) := Nat.cast_nonneg A
      linarith only [hD.1, hScale0, (hRho s).1, (hPk s).1, (hTarget s).1,
        hF, (hMod s).1, hA0])
    calc
      _ ≤ P + scaleBound + P + P + P + (P + 2) + P + A := by
        linarith only [hD.2, hScale, (hRho s).2, (hPk s).2,
          (hTarget s).2, hDetect.2, (hMod s).2]
      _ = _ := by dsimp only [scaleBound]; push_cast; ring
  have hLengthSum0 : 0 ≤ ∑ s, lengthLogs s := Finset.sum_nonneg (fun s _ => hLogs0 s)
  have hLengthSum : (∑ s, lengthLogs s) ≤ ((m + 1 : ℕ) : ℝ) * lengthBound := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using Finset.sum_le_sum (fun s (_ : s ∈ (Finset.univ : Finset (Fin (m + 1)))) => hLengths s)
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
  have hLengthBound0 : 0 ≤ lengthBound := by dsimp only [lengthBound]; positivity
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
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeEarlyBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum pDetect aDetect Qstride : ℝ}
      (target : Fin (m + 1) → ℝ),
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Tmod := fun s : Fin (m + 1) => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : Fin (m + 1) => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : Fin (m + 1) => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2) + 2
      let Ptail := fun s : Fin (m + 1) => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget := by
  let Cs := fun s : Fin (m + 1) =>
    Classical.choose (exists_primitiveCanonicalSliceEarlyScale_budget m s.val (Cdetect s))
  obtain ⟨A, _, hRadius⟩ := exists_allocatedCommonProductRadiusLog_bound m
  let X : Polynomial ℕ := Polynomial.X
  let poly := X + (2 * X + Polynomial.C A) ^ A +
    ∑ s : Fin (m + 1), (X + Polynomial.C (Cs s)) ^ (Cs s)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum pDetect aDetect Qstride target
    hP hB hnum hp ha hQ htarget hcount hnX hG
    pRadius D gainLog Pk Tmod E Prho Ptail budget
  let piece := fun s : Fin (m + 1) => (P + Cs s) ^ Cs s
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
  have hdata (s : Fin (m + 1)) :
      D ∈ Set.Icc 0 budget ∧ gainLog s ∈ Set.Icc 0 budget ∧
      Pk s ∈ Set.Icc 0 budget ∧ Prho s ∈ Set.Icc 0 budget ∧
      Ptail s ∈ Set.Icc 0 budget ∧ Tmod s ∈ Set.Icc 0 budget := by
    obtain ⟨_, hD, hg, hk, hρ, ht, hmod, _, _⟩ :=
      (Classical.choose_spec (exists_primitiveCanonicalSliceEarlyScale_budget m s.val (Cdetect s))).2
        (G := G) hP hnum hp hp ha (htarget s) hQ
        (show (0 : ℝ) ∈ Set.Icc 0 P from ⟨le_rfl, hP⟩) hcount hnX hG
    have lift {x : ℝ} (hx : x ∈ Set.Icc 0 (piece s)) : x ∈ Set.Icc 0 budget :=
      ⟨hx.1, hx.2.trans (hpieceCap s)⟩
    exact ⟨lift hD, lift hg, lift hk, lift hρ, lift ht, lift hmod⟩
  exact ⟨hbase, hradius, (hdata ⟨0, Nat.succ_pos m⟩).1, fun s => (hdata s).2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreeGeometryBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P Bstruct pnum pDetect aDetect Qstride Qσ Pmin Qw : ℝ}
      (target : Fin (m + 1) → ℝ),
      0 ≤ P → Bstruct ∈ Set.Icc 0 P → pnum ∈ Set.Icc 0 P →
      pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P → (∀ s, target s ∈ Set.Icc 0 P) →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      Qσ ∈ Set.Icc 0 P → Pmin ∈ Set.Icc 0 P → Qw ∈ Set.Icc 0 P →
      let pRadius := allocatedCommonProductRadiusLog m Bstruct Bstruct
      let D := allocatedComparisonDimension m pnum
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Tmod := fun s : Fin (m + 1) => ((m + 1 : ℕ) : ℝ) * Pk s + nX * Qstride
      let E := fun s : Fin (m + 1) => target s + D * ((m * 2 ^ (m + 1) : ℕ) * Pk s) + 5
      let Prho := fun s : Fin (m + 1) => 2 * affineProfileInputEnvelope D
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2) + 2
      let Ptail := fun s : Fin (m + 1) => affineProfileToleranceEnvelope m D
        (D * (D + 1) + D * D + D + 1)
        (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E s) (pDetect + 2)
      let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail Qσ
      let lengthLogs := fun s => allocatedAffineLengthLog m D Pscale (Prho s) (Pk s)
        (target s) (pDetect + 2) (Tmod s)
      let Pseed := allocatedScaleLog (Pscale + ∑ s, lengthLogs s + Pmin + 1)
      let budget := (P + C) ^ C
      P ≤ budget ∧ pRadius ∈ Set.Icc 0 budget ∧ D ∈ Set.Icc 0 budget ∧
        (∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          Prho s ∈ Set.Icc 0 budget ∧ Ptail s ∈ Set.Icc 0 budget ∧
          Tmod s ∈ Set.Icc 0 budget) ∧
        Pscale ∈ Set.Icc 0 budget ∧ (∑ s, lengthLogs s) ∈ Set.Icc 0 budget ∧
        Pseed ∈ Set.Icc 0 budget ∧ allocatedWitnessScaleLog Pseed Qw ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedUniformDegreeEarlyBudget m Cdetect
  obtain ⟨L, _, hLate⟩ := exists_preparedUniformDegreePowerBudget m
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let latePoly := (earlyPoly + Polynomial.C L) ^ L
  obtain ⟨C, hC, hBound⟩ := exists_natPolynomial_eval_budget (earlyPoly + latePoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P Bstruct pnum pDetect aDetect Qstride Qσ Pmin Qw target
    hP hB hnum hp ha hQ htarget hcount hnX hG hQσ hPmin hQw
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
    hEarly (G := G) target hP hB hnum hp ha hQ htarget hcount hnX hG
  have lift {x : ℝ} (hx : x ∈ Set.Icc 0 P) : x ∈ Set.Icc 0 early :=
    ⟨hx.1, hx.2.trans hPEarly⟩
  obtain ⟨hScale, hLengths, hSeed, hWitness⟩ :=
    hLate hEarly0 hD hRadius (lift hQσ) (lift hPmin) (lift hQw) (lift hp)
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

section

namespace Erdos3.VectorPolynomial
open scoped Classical BigOperators NNReal

theorem exists_preparedUniformDegreePrecisionBudget
    (m : ℕ) (Cdetect : Fin (m + 1) → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {G : Type} [Fintype G] {count nX : ℕ}
      {P pDetect aDetect Qstride : ℝ},
      0 ≤ P → pDetect ∈ Set.Icc 0 P → aDetect ∈ Set.Icc 0 P →
      Qstride ∈ Set.Icc 0 P →
      (count : ℝ) ≤ P → (nX : ℝ) ≤ P → (Fintype.card G : ℝ) ≤ P →
      let gainLog := fun s : Fin (m + 1) =>
        slicedDetectionGainLog s.val (Cdetect s) count pDetect pDetect aDetect
      let Pk := fun s : Fin (m + 1) =>
        scalarKernelLogarithmicBudget (Fin (s.val + 1)) G (gainLog s + pDetect + 4)
      let Pphysical : ℝ := ((m + 2 : ℕ) : ℝ) + nX + count + Qstride + ∑ s, Pk s
      let target := fun s : Fin (m + 1) =>
        gainLog s + 40 + coefficientErrorSpatialLog Pphysical
      let budget := (P + C) ^ C
      P ≤ budget ∧ Pphysical ∈ Set.Icc 0 budget ∧
        ∀ s, gainLog s ∈ Set.Icc 0 budget ∧ Pk s ∈ Set.Icc 0 budget ∧
          target s ∈ Set.Icc 0 budget := by
  obtain ⟨A, _, hEarly⟩ := exists_preparedUniformDegreeEarlyBudget m Cdetect
  let X : Polynomial ℕ := Polynomial.X
  let earlyPoly := (X + Polynomial.C A) ^ A
  let physicalPoly := Polynomial.C (m + 2) + 3 * X + Polynomial.C (m + 1) * earlyPoly
  let precisionPoly := earlyPoly + 40 + coefficientErrorSpatialLog physicalPoly
  obtain ⟨C, hC, hBound⟩ :=
    exists_natPolynomial_eval_budget (earlyPoly + physicalPoly + precisionPoly)
  refine ⟨C, hC, ?_⟩
  intro G _ count nX P pDetect aDetect Qstride hP hp ha hQ hcount hnX hG
    gainLog Pk Pphysical target budget
  let early := (P + A) ^ A
  let physical : ℝ := ((m + 2 : ℕ) : ℝ) + 3 * P + ((m + 1 : ℕ) : ℝ) * early
  let precision := early + 40 + coefficientErrorSpatialLog physical
  have hearly0 : 0 ≤ early := by dsimp only [early]; positivity
  have hphysical0 : 0 ≤ physical := by dsimp only [physical]; positivity
  have hprecision0 : 0 ≤ precision := by
    have := coefficientErrorSpatialLog_nonneg hphysical0
    dsimp only [precision]
    positivity
  have htotal : early + physical + precision ≤ budget := by
    simpa [X, earlyPoly, physicalPoly, precisionPoly, early, physical, precision,
      coefficientErrorSpatialLog, coefficientErrorVolumeLog, anisotropicSpatialCapLog,
      Polynomial.eval₂_pow] using hBound P hP
  have hearlyCap : early ≤ budget := by linarith only [htotal, hphysical0, hprecision0]
  have hphysicalCap : physical ≤ budget := by linarith only [htotal, hearly0, hprecision0]
  have hprecisionCap : precision ≤ budget := by linarith only [htotal, hearly0, hphysical0]
  have hzero : (0 : ℝ) ∈ Set.Icc 0 P := ⟨le_rfl, hP⟩
  obtain ⟨hPEarly, _, _, hDegrees⟩ :=
    hEarly (G := G) (fun _ => 0) hP hzero hzero hp ha hQ
      (fun _ => hzero) hcount hnX hG
  have hg (s) : gainLog s ∈ Set.Icc 0 early := (hDegrees s).1
  have hk (s) : Pk s ∈ Set.Icc 0 early := (hDegrees s).2.1
  have hsum0 : 0 ≤ ∑ s, Pk s := Finset.sum_nonneg (fun s _ => (hk s).1)
  have hsum : ∑ s, Pk s ≤ ((m + 1 : ℕ) : ℝ) * early := by
    calc
      _ ≤ ∑ _s : Fin (m + 1), early := Finset.sum_le_sum (fun s _ => (hk s).2)
      _ = _ := by simp
  have hactual0 : 0 ≤ Pphysical := by
    have hstride0 := hQ.1
    dsimp only [Pphysical]
    positivity
  have hactual : Pphysical ≤ physical := by
    dsimp only [Pphysical, physical]
    linarith only [hcount, hnX, hQ.2, hsum]
  have hspatial : coefficientErrorSpatialLog Pphysical ≤ coefficientErrorSpatialLog physical := by
    unfold coefficientErrorSpatialLog coefficientErrorVolumeLog anisotropicSpatialCapLog
    gcongr
  refine ⟨hPEarly.trans hearlyCap, ⟨hactual0, hactual.trans hphysicalCap⟩, ?_⟩
  intro s
  refine ⟨⟨(hg s).1, (hg s).2.trans hearlyCap⟩,
    ⟨(hk s).1, (hk s).2.trans hearlyCap⟩, ?_⟩
  constructor
  · have := (hg s).1
    have := coefficientErrorSpatialLog_nonneg hactual0
    dsimp only [target]
    positivity
  · apply le_trans _ hprecisionCap
    dsimp only [target, precision]
    linarith only [(hg s).2, hspatial]

end Erdos3.VectorPolynomial

end

end OAI
