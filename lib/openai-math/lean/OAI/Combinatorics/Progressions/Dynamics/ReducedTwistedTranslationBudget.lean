import OAI.Combinatorics.Progressions.Estimates.MajorRationalLiftInputScale
import OAI.Combinatorics.Progressions.Nilpotent.WeightedTranslationTwistedNiltest

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_weightedTranslationBuffered_scalar_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (n N : ℕ) (p L M : ℝ),
      0 ≤ p → (n : ℝ) ≤ p → N ≤ n + (n + 1) ^ d →
      0 ≤ L → 0 ≤ M → L ≤ Real.exp p → M ≤ Real.exp p →
      ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) ≤ (p + C) ^ C ∧
      2 * max (8 * weightedTranslationDisplacementConstant d n N)
        ((L + 2 * Real.pi * (1 + M * n * d)) *
          weightedTranslationDisplacementConstant d n N) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨Z, hZ, hlog⟩ := exists_bchLogMetricConstant_exp_bound d
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + 1) ^ d + Polynomial.C (d.factorial + 2 * d + 1)
  let K := Polynomial.C d *
    (1 + (X + 1) * (Polynomial.C (d + 1) * (X + 2) ^ d) * Polynomial.C d) ^ d
  let P := Q + K + (Q + Polynomial.C Z) ^ Z + 3 * X + Polynomial.C (d + 15)
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro n N p L M hp hn hN hL hM hLp hMp
  let q : ℝ := p + (p + 1) ^ d + (d.factorial + 2 * d + 1 : ℕ)
  let k : ℝ := d * (1 + (p + 1) * (((d : ℝ) + 1) * (p + 2) ^ d) * d) ^ d
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have htotal : q + k + (q + Z) ^ Z + 3 * p + (d + 15 : ℕ) ≤ (p + C) ^ C := by
    simpa [X, Q, K, P, q, k, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul] using hbudget p hp
  have hgeom : ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) ≤ q := by
    have hpow : ((n : ℝ) + 1) ^ d ≤ (p + 1) ^ d :=
      pow_le_pow_left₀ (by positivity) (by linarith) d
    dsimp [q]
    push_cast
    linarith
  have hdim : (N : ℝ) ≤ q := by
    apply (Nat.cast_le.mpr hN).trans
    have hh : ((n + (n + 1) ^ d : ℕ) : ℝ) ≤
        ((n + (n + 1) ^ d + d.factorial + 2 * d + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n + (n + 1)^d ≤ n + (n+1)^d + d.factorial + 2*d + 1)
    exact hh.trans hgeom
  have hHq : ((2 * d + 1 : ℕ) : ℝ) ≤ q := by
    dsimp [q]
    have hd0 := Nat.cast_nonneg (α := ℝ) d.factorial
    have hpow : 0 ≤ (p + 1) ^ d := by positivity
    push_cast
    linarith
  have hHexp : ((2 * d + 1 : ℕ) : ℝ) ≤ Real.exp q :=
    hHq.trans (by linarith [Real.add_one_le_exp q])
  have hlogbound := hlog N (2 * d + 1) q hq hdim hHexp
  have hshear : (polynomialShearDisplacementBound d (n + 1) 1 : ℝ) ≤ k := by
    dsimp [polynomialShearDisplacementBound, k]
    push_cast
    simp only [one_pow, mul_one]
    simp only [add_assoc, one_add_one_eq_two]
    gcongr
  have hshear1 : (polynomialShearDisplacementBound d (n + 1) 1 : ℝ) + 1 ≤ Real.exp k := by
    linarith [Real.add_one_le_exp k]
  have hv : 0 ≤ (q + Z) ^ Z + 1 := by positivity
  have hlog1 : (bchLogMetricConstant d N (2 * d + 1) 1 : ℝ) + 1 ≤
      Real.exp ((q + Z) ^ Z + 2) := by
    have hh := one_add_le_exp_succ hv hlogbound
    simpa only [add_comm (1 : ℝ), add_assoc, one_add_one_eq_two] using hh
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hdisp : weightedTranslationDisplacementConstant d n N ≤
      Real.exp (k + (q + Z) ^ Z + 3) := by
    unfold weightedTranslationDisplacementConstant
    calc
      _ ≤ Real.exp 1 * Real.exp k * Real.exp ((q + Z) ^ Z + 2) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hnp : (n : ℝ) ≤ Real.exp p := hn.trans (by linarith [Real.add_one_le_exp p])
  have hdp : (d : ℝ) ≤ Real.exp d := by linarith [Real.add_one_le_exp (d : ℝ)]
  have hprod : M * (n : ℝ) * d ≤ Real.exp (2 * p + d) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp d := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hprod1 : 1 + M * (n : ℝ) * d ≤ Real.exp (2 * p + d + 1) :=
    one_add_le_exp_succ (by positivity) hprod
  have hpi : 2 * Real.pi ≤ Real.exp 8 := by
    have hp4 := Real.pi_le_four
    linarith [Real.add_one_le_exp (8 : ℝ)]
  have hphase : 2 * Real.pi * (1 + M * (n : ℝ) * d) ≤ Real.exp (2 * p + d + 9) := by
    calc
      _ ≤ Real.exp 8 * Real.exp (2 * p + d + 1) := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hsum : L + 2 * Real.pi * (1 + M * (n : ℝ) * d) ≤ Real.exp (3 * p + d + 10) := by
    have hh := add_le_exp_add_one hp (by positivity : 0 ≤ 2 * p + d + 9) hLp hphase
    convert hh using 1; congr 1; ring
  have height : (8 : ℝ) ≤ Real.exp (3 * p + d + 10) := by
    have hh := Real.add_one_le_exp (3 * p + d + 10)
    have hd0 := Nat.cast_nonneg (α := ℝ) d
    linarith
  have hmax : max (8 * weightedTranslationDisplacementConstant d n N)
      ((L + 2 * Real.pi * (1 + M * n * d)) * weightedTranslationDisplacementConstant d n N) ≤
        Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3) := by
    apply max_le
    · exact mul_le_mul height hdisp (weightedTranslationDisplacementConstant_pos _ _ _).le (Real.exp_nonneg _)
    · exact mul_le_mul hsum hdisp (weightedTranslationDisplacementConstant_pos _ _ _).le (Real.exp_nonneg _)
  constructor
  · apply hgeom.trans
    have hz : 0 ≤ (q + Z) ^ Z := by positivity
    have hd0 := Nat.cast_nonneg (α := ℝ) (d + 15)
    linarith
  · calc
      _ ≤ 2 * (Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3)) :=
        mul_le_mul_of_nonneg_left hmax (by norm_num)
      _ ≤ Real.exp 1 * (Real.exp (3 * p + d + 10) * Real.exp (k + (q + Z) ^ Z + 3)) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = Real.exp (k + (q + Z) ^ Z + 3 * p + d + 14) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((p + C) ^ C) := by
        apply Real.exp_le_exp.mpr
        push_cast at htotal
        linarith

theorem exists_weightedTranslationBuffered_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      (Ψ : PatchKernel m) (M : ℝ≥0) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (Ψ.lip : ℝ) ≤ Real.exp p → (M : ℝ) ≤ Real.exp p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE ((p + C) ^ C) ∧
      ((2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ := exists_weightedTranslationBuffered_scalar_budget d
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ Ψ M p hp hm hΨ hM
  have hcard : Fintype.card (WeightedBasisIndex w d) ≤ m + (m + 1) ^ d := by
    simpa only [Fintype.card_fin] using weightedBasisIndex_card_le w d hw
  obtain ⟨hgeometry, hlip⟩ := hbound m (Fintype.card (WeightedBasisIndex w d)) p
    Ψ.lip M hp hm hcard Ψ.lip.coe_nonneg M.coe_nonneg hΨ hM
  constructor
  · apply RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (weightedTranslationNilmanifold w d hw hwd)
      (weightedTranslationNilmanifold_complexity_budget w d hw hwd)
    simpa only [Fintype.card_fin] using hgeometry
  · change 2 * max (8 * weightedTranslationDisplacementConstant d m
        (Fintype.card (WeightedBasisIndex w d)))
      (((Ψ.lip : ℝ) + 2 * Real.pi * (1 + (M : ℝ) * m * d)) *
        weightedTranslationDisplacementConstant d m
          (Fintype.card (WeightedBasisIndex w d))) ≤ _
    exact hlip

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal TensorProduct

theorem twistedBufferedTranslation_log_bound {m : ℕ} (w : Fin m → ℕ) (d : ℕ)
    [Fintype (WeightedBasisIndex w d)] (Ψ : PatchKernel m) (A K : ℝ≥0)
    {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r)
    (hB : ((2 * bufferedTranslationTermLip w d Ψ A : ℝ≥0) : ℝ) ≤ Real.exp r)
    (hK : (K : ℝ) ≤ Real.exp p) :
    Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ)) ≤
      p + r + 6 := by
  let B : ℝ := bufferedTranslationTermLip w d Ψ A
  let C : ℝ := translationDisplacementNN w d
  have hBn : 0 ≤ B := NNReal.coe_nonneg _
  have hCn : 0 ≤ C := NNReal.coe_nonneg _
  have hCB : C ≤ B := by
    have hh : 8 * C ≤ B := le_max_left _ _
    linarith
  change 2 * B ≤ Real.exp r at hB
  have hBe : B ≤ Real.exp r := by linarith
  have hCe : C ≤ Real.exp r := hCB.trans hBe
  have hBpr : B ≤ Real.exp (p + r) :=
    hBe.trans (Real.exp_le_exp.mpr (by linarith))
  have hCpr : C ≤ Real.exp (p + r) := hCB.trans hBpr
  have hKC : (K : ℝ) * C ≤ Real.exp (p + r) := by
    rw [Real.exp_add]
    exact mul_le_mul hK hCe hCn (Real.exp_nonneg _)
  have hmax : max (2 * C) (B + (K : ℝ) * C) ≤ 2 * Real.exp (p + r) := by
    exact max_le (by linarith) (by linarith)
  have hfour : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hLip : ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ) ≤
      Real.exp (p + r + 3) := by
    change 2 * max (2 * C) (B + (K : ℝ) * C) ≤ _
    calc
      _ ≤ 4 * Real.exp (p + r) := by linarith
      _ ≤ Real.exp 3 * Real.exp (p + r) :=
        mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    _ ≤ 4 * Real.exp (p + r + 3) := by
      linarith [Real.one_le_exp (show 0 ≤ p + r + 3 by linarith)]
    _ ≤ Real.exp 3 * Real.exp (p + r + 3) :=
      mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_weightedTwistedTranslation_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m) (A K : ℝ≥0) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (M : ℝ) ≤ Real.exp p →
      (Ψ.lip : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p → (K : ℝ) ≤ Real.exp p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ A K : ℝ≥0) : ℝ)) ≤
        (p + C) ^ C := by
  obtain ⟨a, _, hbuffer⟩ := exists_weightedTranslationBuffered_budget d
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + X + 6)
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ M hM Ψ A K p hp hm hMp hΨ hA hK
  obtain ⟨hG, hB⟩ := hbuffer w hw hwd Ψ A p hp hm hΨ hA
  have hbound : (p + a) ^ a + p + 6 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hlogM : Real.log (M : ℝ) ≤ p :=
    (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hM)).mpr hMp
  constructor
  · apply RationalFilteredNilmanifold.GeometryComplexityLE.mono
      (weightedTranslationResidueNilmanifold w d hw hwd M hM)
      (weightedTranslationResidueNilmanifold_complexity_add_log w d hw hwd M hM hG)
    linarith
  · exact (twistedBufferedTranslation_log_bound w d Ψ A K hp (by positivity) hB hK).trans
      (by linarith)

theorem exists_weightedTranslationTwistedNiltest_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} (w : Fin m → ℕ) (hw : ∀ i, 0 < w i)
      (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      (M : ℕ) (hM : 0 < M) {U : Type*} (ω : U → ℕ) (hd : 0 < d)
      (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (A K : ℝ≥0)
      (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ A)
      (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (hT : ∀ x r, ‖T x r‖ ≤ 1) (hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (p : ℝ),
      0 ≤ p → (m : ℝ) ≤ p → (M : ℝ) ≤ Real.exp p →
      (Ψ.lip : ℝ) ≤ Real.exp p → (A : ℝ) ≤ Real.exp p → (K : ℝ) ≤ Real.exp p →
      (weightedTranslationTwistedNiltest w d hw hwd M hM ω hd Ψ D₀ A K hdegree hD
        T hT hLip q).ComplexityLE ((p + C) ^ C) := by
  obtain ⟨C, hC, hbudget⟩ := exists_weightedTwistedTranslation_budget d
  refine ⟨C, hC, ?_⟩
  intro m w hw hwd _ _ _ _ _ M hM U ω hd Ψ D₀ A K hdegree hD T hT hLip q p
    hp hm hMp hΨ hA hK
  obtain ⟨hgeometry, hbound⟩ := hbudget w hw hwd M hM Ψ A K p hp hm hMp hΨ hA hK
  exact weightedTranslationTwistedNiltest_complexity w d hw hwd M hM ω hd Ψ D₀ A K
    hdegree hD T hT hLip q hgeometry hbound

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_majorRationalLift_detection_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U : Type*} [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
      (Ψ : PatchKernel m) (a : Fin m → ℤ) (p : ℝ),
      0 ≤ p → ((Fintype.card U + m : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d)
        (rationalLiftCharacterTwistLip M a) : ℝ≥0) : ℝ)) ≤ (p + C) ^ C := by
  obtain ⟨b, _, htwisted⟩ := exists_weightedTwistedTranslation_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q : Polynomial ℕ :=
    (Polynomial.C (d + 2) * (X + 1) + 8 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ M hM Ψ a p hp hdim hMexp hΨ ha
  let q : ℝ := majorRationalLiftInputScale d p
  have hq := majorRationalLiftInputScale_bounds d p hp
  have hmp : (m : ℝ) ≤ p := by
    have hsum : (m : ℝ) ≤ ((Fintype.card U + m : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hsum.trans hdim
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  have hB : (B : ℝ) ≤ Real.exp q :=
    majorRationalLiftInputScale_mass d p hp (Fintype.card U) m hdim
  have hK : (rationalLiftCharacterTwistLip M a : ℝ) ≤ Real.exp q := by
    apply (rationalLiftCharacterTwistLip_le_exp_of_dim M hM a p p hmp ha).trans
    apply Real.exp_le_exp.mpr
    change p + p + 8 ≤ majorRationalLiftInputScale d p
    linarith [hq.2.2]
  obtain ⟨hgeometry, hlog⟩ := htwisted w hw hwd M hM Ψ B
    (rationalLiftCharacterTwistLip M a) q hq.1 (hmp.trans hq.2.1)
    (hMexp.trans (Real.exp_le_exp.mpr hq.2.1))
    (hΨ.trans (Real.exp_le_exp.mpr hq.2.1)) hB hK
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, X, q, majorRationalLiftInputScale, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _ hgeometry hcost,
    hlog.trans hcost⟩

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open scoped NNReal

theorem exists_reducedTwistedTranslation_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (U : Type*) [Fintype U] {m : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      (M : ℕ) (hM : 0 < M) (Ψ : PatchKernel m) (K : ℝ≥0) (p : ℝ),
      0 ≤ p → ((Fintype.card U + m : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (K : ℝ) ≤ Real.exp p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE
        ((p + C) ^ C) ∧
      Real.log (3 + ((2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0) : ℝ)) ≤
        (p + C) ^ C := by
  obtain ⟨a, _, hbudget⟩ := exists_weightedTwistedTranslation_budget d
  let X : Polynomial ℕ := Polynomial.X
  let Q := (Polynomial.C (d + 1) * (X + 1) + Polynomial.C a) ^ a
  obtain ⟨C, hC, hCbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro U _ m w hw hwd _ M hM Ψ K p hp hdim hMp hΨ hK
  let B : ℝ≥0 := ((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d
  let q : ℝ := (d + 1 : ℕ) * (p + 1)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    dsimp [q]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hm : (m : ℝ) ≤ q := by
    have hh : (m : ℝ) ≤ (Fintype.card U + m : ℕ) := by
      exact_mod_cast Nat.le_add_left m (Fintype.card U)
    exact hh.trans (hdim.trans hpq)
  have hB : (B : ℝ) ≤ Real.exp q := by
    have hb : ((Fintype.card U + m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
      push_cast at hdim ⊢
      linarith [Real.add_one_le_exp (p + 1)]
    calc
      (B : ℝ) ≤ (Real.exp (p + 1)) ^ d := by
        change (((Fintype.card U + m + 1 : ℕ) : ℝ) ^ d) ≤ _
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb d
      _ = Real.exp ((d : ℝ) * (p + 1)) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp q := by apply Real.exp_le_exp.mpr; dsimp [q]; push_cast; nlinarith
  obtain ⟨hgeometry, hlog⟩ := hbudget w hw hwd M hM Ψ B K q hq hm
    (hMp.trans (Real.exp_le_exp.mpr hpq)) (hΨ.trans (Real.exp_le_exp.mpr hpq))
    hB (hK.trans (Real.exp_le_exp.mpr hpq))
  have hcost : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hCbudget p hp
  exact ⟨RationalFilteredNilmanifold.GeometryComplexityLE.mono _ hgeometry hcost,
    hlog.trans hcost⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
