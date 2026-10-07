import OAI.Combinatorics.Progressions.Estimates.ScalarInitialThreshold

namespace OAI

section

namespace Erdos3

theorem canonicalScalarTarget_dimension_bounds (d : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let T := 8 * ((d : ℝ)+1) * (p+1)
    p ≤ T ∧ ∀ n : ℕ, (n : ℝ) ≤ p → 4 * ((d : ℝ)*n+1) ≤ T := by
  intro T
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hdp : 0 ≤ (d : ℝ)*p := mul_nonneg hd hp
  constructor
  · dsimp [T]
    nlinarith
  · intro n hn
    have hdn := mul_le_mul_of_nonneg_left hn hd
    dsimp [T]
    nlinarith

theorem exists_canonicalScalarFinalBudget (d A C : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ {p : ℝ}, 0 ≤ p →
      let T := 8 * ((d : ℝ)+1) * (p+1)
      let P0 := (A : ℝ) * (T+1)
      let budget := (T+2)^C
      ((d : ℝ)+4) * (budget+P0+20) ≤ (p+D)^D ∧
        budget ≤ (p+D)^D := by
  let T : Polynomial ℕ := 8 * (Polynomial.C d + 1) * (Polynomial.X + 1)
  let Q : Polynomial ℕ := (Polynomial.C d + 4) *
    ((T+2)^C + Polynomial.C A * (T+1) + 20)
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨D, hD, ?_⟩
  intro p hp target P0 budget
  have hcost : ((d : ℝ)+4) * (budget+P0+20) ≤ (p+D)^D := by
    simpa [Q, T, target, P0, budget, Polynomial.eval₂_pow] using hbound p hp
  have ht : 0 ≤ target := by dsimp [target]; positivity
  have hP : 0 ≤ P0 := by dsimp [P0]; positivity
  have hb : 0 ≤ budget := by dsimp [budget]; positivity
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  refine ⟨hcost, le_trans ?_ hcost⟩
  nlinarith [mul_nonneg hd (add_nonneg hb hP)]

end Erdos3

end

section

namespace Erdos3

theorem exists_canonicalScalarPrimitiveLogBudget (d marginFactor : ℕ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ A : ℕ, 3 ≤ A ∧ ∀ {p σ : ℝ} {n : ℕ}, 2 ≤ p →
      (n : ℝ) ≤ p → 0 < σ → σ⁻¹ ≤ Real.exp p →
      let P0 := (A : ℝ) * (p + 1)
      let τ := σ / ((marginFactor : ℝ) * ((n : ℝ) + 1))
      0 ≤ P0 ∧ 3*p+10 ≤ P0 ∧ epsilon⁻¹ ≤ Real.exp P0 ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 ∧
      (d : ℝ) ≤ Real.exp P0 ∧ 2 ≤ Real.exp P0 ∧
      τ⁻¹ ≤ Real.exp P0 ∧ 16 * (2*(d : ℝ)+1) / τ ≤ Real.exp P0 := by
  let M : ℝ := epsilon⁻¹ + (probabilityProfileLipschitz : ℝ) + d +
    marginFactor + 16*(2*(d : ℝ)+1)*marginFactor + 16
  let A : ℕ := ⌈M⌉₊ + 3
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hMA : M ≤ (A : ℝ) := by
    have hh := Nat.le_ceil M
    dsimp [A]
    push_cast
    linarith
  have hA : 3 ≤ A := by dsimp [A]; omega
  refine ⟨A, hA, ?_⟩
  intro p σ n hp hn hσ hσb P0 τ
  have hp0 : 0 ≤ p := by linarith
  have heps0 : 0 ≤ epsilon⁻¹ := inv_nonneg.mpr hepsilon.le
  have hprof0 : 0 ≤ (probabilityProfileLipschitz : ℝ) := probabilityProfileLipschitz.coe_nonneg
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ marginFactor := Nat.cast_nonneg _
  have hconst0 : 0 ≤ 16*(2*(d : ℝ)+1)*(marginFactor : ℝ) := by positivity
  have hA16 : (16 : ℝ) ≤ A := by dsimp [M] at hMA; linarith
  have hP0 : 0 ≤ P0 := by dsimp [P0]; positivity
  have hAP0 : (A : ℝ) ≤ P0 := by dsimp [P0]; nlinarith
  have hexp : (A : ℝ) ≤ Real.exp P0 :=
    hAP0.trans (by linarith [Real.add_one_le_exp P0])
  have hscale : (A : ℝ) + 2*p ≤ P0 := by dsimp [P0]; nlinarith
  have hmul (c : ℝ) (hc0 : 0 ≤ c) (hc : c ≤ (A : ℝ)) :
      c * Real.exp (2*p) ≤ Real.exp P0 := by
    have hcExp : c ≤ Real.exp (A : ℝ) :=
      hc.trans (by linarith [Real.add_one_le_exp (A : ℝ)])
    calc
      _ ≤ Real.exp (A : ℝ) * Real.exp (2*p) :=
        mul_le_mul_of_nonneg_right hcExp (Real.exp_nonneg _)
      _ = Real.exp ((A : ℝ)+2*p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hscale
  have hnexp : (n : ℝ)+1 ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hinv : τ⁻¹ = (marginFactor : ℝ) * ((n : ℝ)+1) * σ⁻¹ := by
    dsimp [τ]
    rw [inv_div, div_eq_mul_inv]
  have hτbound : τ⁻¹ ≤ (marginFactor : ℝ) * Real.exp (2*p) := by
    rw [hinv]
    calc
      _ ≤ (marginFactor : ℝ) * Real.exp p * Real.exp p := by gcongr
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hKbound : 16*(2*(d : ℝ)+1)/τ ≤
      (16*(2*(d : ℝ)+1)*(marginFactor : ℝ)) * Real.exp (2*p) := by
    rw [div_eq_mul_inv]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hτbound
      (show 0 ≤ 16*(2*(d : ℝ)+1) by positivity)
  refine ⟨hP0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [P0]
    nlinarith
  · apply le_trans _ hexp
    dsimp [M] at hMA
    linarith
  · apply le_trans _ hexp
    dsimp [M] at hMA
    linarith
  · apply le_trans _ hexp
    dsimp [M] at hMA
    linarith
  · linarith
  · apply hτbound.trans (hmul _ hf0 ?_)
    dsimp [M] at hMA
    linarith
  · apply hKbound.trans (hmul _ hconst0 ?_)
    dsimp [M] at hMA
    linarith

end Erdos3

end

section

namespace Erdos3

theorem exists_canonicalScalarSelectedBudget (E d : ℕ) (hE : 2 ≤ E)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ (n : ℕ) {p σ : ℝ}, 2 ≤ p → (n : ℝ) ≤ p →
      0 < σ → σ⁻¹ ≤ Real.exp p →
    let target := 8 * ((d : ℝ) + 1) * (p + 1)
    let P0 := (A : ℝ) * (target + 1)
    let budget := (target + 2) ^ C
    let τ := unconditionedSpatialTrimFraction n σ
    p ≤ target ∧ 2 ≤ target ∧ (n : ℝ) ≤ target ∧
      4 * ((d : ℝ) * n + 1) ≤ target ∧
      0 ≤ P0 ∧ 3 * target + 10 ≤ P0 ∧
      epsilon⁻¹ ≤ Real.exp P0 ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 ∧
      (d : ℝ) ≤ Real.exp P0 ∧ 2 ≤ Real.exp P0 ∧
      τ⁻¹ ≤ Real.exp P0 ∧ 16 * (2 * (d : ℝ) + 1) / τ ≤ Real.exp P0 ∧
      0 ≤ budget ∧
      scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget ∧
      ((d : ℝ) + 4) * (budget + P0 + 20) ≤ (p + F) ^ F ∧
      budget ≤ (p + F) ^ F := by
  obtain ⟨A, hA, hprimitive⟩ := exists_canonicalScalarPrimitiveLogBudget d 32 hepsilon
  obtain ⟨C, hC, hthreshold⟩ := exists_scalarInitialThreshold_power E d A hE hepsilon hepsilon1
  obtain ⟨F, hF, hfinal⟩ := exists_canonicalScalarFinalBudget d A C
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro n p σ hp hn hσ hσinv target P0 budget τ
  have hp0 : 0 ≤ p := by linarith
  have ht := canonicalScalarTarget_dimension_bounds d hp0
  have hpTarget : p ≤ target := ht.1
  have htarget : 2 ≤ target := hp.trans hpTarget
  have hnTarget : (n : ℝ) ≤ target := hn.trans hpTarget
  have hσTarget : σ⁻¹ ≤ Real.exp target := hσinv.trans (Real.exp_le_exp.mpr hpTarget)
  obtain ⟨hP0, htargetP0, hepsP0, hprofile, hdP0, htwoP0, hτP0, hKP0⟩ :=
    hprimitive htarget hnTarget hσ hσTarget
  have hbudget0 : 0 ≤ budget := pow_nonneg (by linarith) _
  have hbudget : scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget := by
    apply hthreshold _ _ target htarget _ hnTarget hepsP0
    push_cast
    gcongr
  exact ⟨hpTarget, htarget, hnTarget, ht.2 n hn, hP0, htargetP0, hepsP0, hprofile,
    hdP0, htwoP0, hτP0, hKP0, hbudget0, hbudget, (hfinal hp0).1, (hfinal hp0).2⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_comparableScalarSelectedBudget (E d r : ℕ)
    (hE : 2 ≤ E) (hd : 2 ≤ d) (hr : 2 ≤ r)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hepsilon1 : epsilon ≤ 1) :
    ∃ A C F : ℕ, 3 ≤ A ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ (n : ℕ) {p σ : ℝ}, 2 ≤ p → (n : ℝ) ≤ p →
      0 < σ → σ⁻¹ ≤ Real.exp p →
    let D := r * d
    let target := 8 * ((D : ℝ) + 1) * (p + 1)
    let P0 := (A : ℝ) * (target + 1)
    let budget := (target + 2) ^ C
    let τ := unconditionedSpatialTrimFraction n σ
    p ≤ target ∧ 2 ≤ target ∧ (n : ℝ) ≤ target ∧
      4 * ((d : ℝ) * n + 1) ≤ target ∧
      0 ≤ P0 ∧ 3 * target + 10 ≤ P0 ∧
      epsilon⁻¹ ≤ Real.exp P0 ∧
      (probabilityProfileLipschitz : ℝ) ≤ Real.exp P0 ∧
      (D : ℝ) ≤ Real.exp P0 ∧ (d : ℝ) ≤ Real.exp P0 ∧
      (r : ℝ) + 1 ≤ Real.exp P0 ∧ 2 ≤ Real.exp P0 ∧
      τ⁻¹ ≤ Real.exp P0 ∧ 16 * (2 * (D : ℝ) + 1) / τ ≤ Real.exp P0 ∧
      0 ≤ budget ∧
      scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget ∧
      ((D : ℝ) + 4) * (budget + P0 + 20) ≤ (p + F) ^ F ∧
      budget ≤ (p + F) ^ F := by
  obtain ⟨A, hA, hprimitive⟩ := exists_canonicalScalarPrimitiveLogBudget (r*d) 32 hepsilon
  obtain ⟨C, hC, hthreshold⟩ := exists_scalarInitialThreshold_power E d A hE hepsilon hepsilon1
  obtain ⟨F, hF, hfinal⟩ := exists_canonicalScalarFinalBudget (r*d) A C
  refine ⟨A, C, F, hA, hC, hF, ?_⟩
  intro n p σ hp hn hσ hσinv D target P0 budget τ
  have hp0 : 0 ≤ p := by linarith
  have hdD : d ≤ D := by
    have hh := Nat.mul_le_mul_right d hr
    dsimp [D]
    omega
  have hrD : r+1 ≤ D := by
    have hh := Nat.mul_le_mul_left r hd
    dsimp [D]
    omega
  have ht := canonicalScalarTarget_dimension_bounds D hp0
  have hpTarget : p ≤ target := ht.1
  have htarget : 2 ≤ target := hp.trans hpTarget
  have hnTarget : (n : ℝ) ≤ target := hn.trans hpTarget
  have hσTarget : σ⁻¹ ≤ Real.exp target := hσinv.trans (Real.exp_le_exp.mpr hpTarget)
  obtain ⟨hP0, htargetP0, hepsP0, hprofile, hDP0, htwoP0, hτP0, hKP0⟩ :=
    hprimitive htarget hnTarget hσ hσTarget
  have hdP0 : (d : ℝ) ≤ Real.exp P0 := (Nat.cast_le.mpr hdD).trans hDP0
  have hrP0 : (r : ℝ)+1 ≤ Real.exp P0 := by
    have hh : ((r+1 : ℕ) : ℝ) ≤ Real.exp P0 := (Nat.cast_le.mpr hrD).trans hDP0
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hframe : 4 * ((d : ℝ)*n+1) ≤ target := by
    apply le_trans _ (ht.2 n hn)
    gcongr
  have hbudget0 : 0 ≤ budget := pow_nonneg (by linarith) _
  have hbudget : scalarInitialThreshold E ((d + 1) * n) n d epsilon target P0 ≤ budget := by
    apply hthreshold _ _ target htarget _ hnTarget hepsP0
    push_cast
    gcongr
  exact ⟨hpTarget, htarget, hnTarget, hframe, hP0, htargetP0, hepsP0, hprofile,
    hDP0, hdP0, hrP0, htwoP0, hτP0, hKP0, hbudget0, hbudget,
    (hfinal hp0).1, (hfinal hp0).2⟩

end Erdos3

end

end OAI
