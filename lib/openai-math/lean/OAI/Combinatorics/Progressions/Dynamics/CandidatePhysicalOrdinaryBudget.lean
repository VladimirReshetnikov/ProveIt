import OAI.Combinatorics.Progressions.Estimates.NativeOptionTargetObservableRegularity
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffineCanonicalBackendBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedCandidateTerminalFullInput
    (s m Cprimitive : ℕ) (x work cumulative : ℝ) : ℝ :=
  (x + Cprimitive) ^ Cprimitive + x + work +
    s * m * certifiedAffineCenterBudget cumulative +
    certifiedAffineCenterBudget cumulative + s + m + 10

private theorem terminal_affine_budget_arithmetic {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ 2 * c + a + b + 1 ∧ b ≤ 2 * c + a + b + 1 := by
  constructor <;> linarith only [hc, ha, hb]

private theorem terminal_affine_budget_bounds {cumulative : ℝ} (hc : 0 ≤ cumulative) :
    0 ≤ certifiedAffineCenterBudget cumulative ∧
    ((cumulative + ((cumulative + 2) ^ 2 + 2) ^ 63) + 2) ^ 8 ≤
      certifiedAffineCenterBudget cumulative := by
  exact terminal_affine_budget_arithmetic hc (by positivity) (by positivity)

attribute [local irreducible] certifiedAffineCenterBudget

theorem allocatedCandidateTerminalFullInput_bounds
    (s m Cprimitive : ℕ) {x work cumulative : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ work) (hc : 0 ≤ cumulative) :
    let p := allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative
    0 ≤ p ∧ (x + Cprimitive) ^ Cprimitive ≤ p ∧ x ≤ p ∧ work ≤ p ∧
      (s : ℝ) ≤ p ∧ (m : ℝ) ≤ p ∧ certifiedAffineCenterBudget cumulative ≤ p ∧
      work + s * m * certifiedAffineCenterBudget cumulative ≤ p := by
  have hB := (terminal_affine_budget_bounds hc).1
  have hbase : 0 ≤ (x + Cprimitive) ^ Cprimitive := by positivity
  have hprod : 0 ≤ (s : ℝ) * m * certifiedAffineCenterBudget cumulative := by positivity
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp only [allocatedCandidateTerminalFullInput]
  exact ⟨by linarith only [hbase, hx, hw, hprod, hB, hs, hm],
    by linarith only [hx, hw, hprod, hB, hs, hm],
    by linarith only [hbase, hw, hprod, hB, hs, hm],
    by linarith only [hbase, hx, hprod, hB, hs, hm],
    by linarith only [hbase, hx, hw, hprod, hB, hm],
    by linarith only [hbase, hx, hw, hprod, hB, hs],
    by linarith only [hbase, hx, hw, hprod, hs, hm],
    by linarith only [hbase, hx, hB, hs, hm]⟩

theorem allocatedCandidateTerminalFullInput_denominator_bound
    (s m Cprimitive : ℕ) {x work cumulative : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ work) (hc : 0 ≤ cumulative) :
    Real.exp work * (Real.exp ((m : ℝ) * certifiedAffineCenterBudget cumulative)) ^ s ≤
      Real.exp (allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative) := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [mul_assoc] using
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hw hc).2.2.2.2.2.2.2

private theorem terminal_mass_budget_bound (m nVars : ℕ) {p H : ℝ}
    (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hn : (nVars : ℝ) ≤ p) (hH : H ≤ p) :
    actualCandidateSlowProjectionMassBudget m nVars p H ≤ Real.exp (p ^ 2 + 4 * p + 3) := by
  have hpExp : p ≤ Real.exp p := by linarith only [Real.add_one_le_exp p]
  have hmExp : ((m + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hm, Real.add_one_le_exp (p + 1)]
  have hnExp : ((nVars + 1 : ℕ) : ℝ) ≤ Real.exp (p + 1) := by
    simp only [Nat.cast_add, Nat.cast_one]
    linarith only [hn, Real.add_one_le_exp (p + 1)]
  have hnPow : (((nVars + 1 : ℕ) : ℝ) ^ m) ≤ Real.exp ((m : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) hnExp m
  have hmain : p * Real.exp H *
      (((m + 1 : ℕ) : ℝ) * ((nVars + 1 : ℕ) : ℝ) ^ m) ≤
        Real.exp (p ^ 2 + 4 * p + 1) := by
    calc
      _ ≤ Real.exp p * Real.exp p *
          (Real.exp (p + 1) * Real.exp ((m : ℝ) * (p + 1))) :=
        mul_le_mul
          (mul_le_mul hpExp (Real.exp_le_exp.mpr hH) (Real.exp_nonneg _) (Real.exp_nonneg _))
          (mul_le_mul hmExp hnPow (by positivity) (Real.exp_nonneg _))
          (by positivity) (by positivity)
      _ = Real.exp (p + p + ((p + 1) + (m : ℝ) * (p + 1))) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hmul := mul_le_mul_of_nonneg_right hm (by linarith only [hp] : 0 ≤ p + 1)
        nlinarith only [hmul]
  have hQ : 0 ≤ p ^ 2 + 4 * p + 1 := by positivity
  have hone := Real.one_le_exp hQ
  have hthree : (3 : ℝ) ≤ Real.exp 2 := by
    linarith only [Real.add_one_le_exp (2 : ℝ)]
  unfold actualCandidateSlowProjectionMassBudget
  calc
    _ ≤ 2 + Real.exp (p ^ 2 + 4 * p + 1) := add_le_add le_rfl hmain
    _ ≤ 3 * Real.exp (p ^ 2 + 4 * p + 1) := by linarith only [hone]
    _ ≤ Real.exp 2 * Real.exp (p ^ 2 + 4 * p + 1) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem actualCandidateSlowProjectionMassBudget_terminal_bound
    (s m nTags nVars : ℕ) {p work H : ℝ}
    (hp : 0 ≤ p) (hs : (s : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (htags : (nTags : ℝ) ≤ p) (hvars : (nVars : ℝ) ≤ p)
    (hwork : work ≤ p) (hH : H ≤ p) :
    ((nTags : ℝ) + 1) ^ s * Real.exp work *
      (actualCandidateSlowProjectionMassBudget m nVars p H) ^ s ≤
        Real.exp ((p + 2) ^ 4) := by
  have htagsExp : (nTags : ℝ) + 1 ≤ Real.exp (p + 1) := by
    linarith only [htags, Real.add_one_le_exp (p + 1)]
  have htagsPow : ((nTags : ℝ) + 1) ^ s ≤ Real.exp ((s : ℝ) * (p + 1)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ (by positivity) htagsExp s
  have hmass := terminal_mass_budget_bound m nVars hp hm hvars hH
  have hmass0 : 0 ≤ actualCandidateSlowProjectionMassBudget m nVars p H :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (actualCandidateSlowProjectionMassBudget_one_le m nVars hp)
  have hmassPow : (actualCandidateSlowProjectionMassBudget m nVars p H) ^ s ≤
      Real.exp ((s : ℝ) * (p ^ 2 + 4 * p + 3)) := by
    simpa only [Real.exp_nat_mul] using pow_le_pow_left₀ hmass0 hmass s
  calc
    _ ≤ Real.exp ((s : ℝ) * (p + 1)) * Real.exp p *
        Real.exp ((s : ℝ) * (p ^ 2 + 4 * p + 3)) :=
      mul_le_mul
        (mul_le_mul htagsPow (Real.exp_le_exp.mpr hwork) (Real.exp_nonneg _) (Real.exp_nonneg _))
        hmassPow (pow_nonneg hmass0 _) (by positivity)
    _ = Real.exp ((s : ℝ) * (p + 1) + p + s * (p ^ 2 + 4 * p + 3)) := by
      rw [← Real.exp_add, ← Real.exp_add]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hs1 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ p + 1)
      have hs2 := mul_le_mul_of_nonneg_right hs (by positivity : 0 ≤ p ^ 2 + 4 * p + 3)
      have hpoly : p * (p + 1) + p + p * (p ^ 2 + 4 * p + 3) ≤ (p + 2) ^ 4 := by
        nlinarith only [hp, sq_nonneg p, pow_nonneg hp 3, pow_nonneg hp 4]
      linarith only [hs1, hs2, hpoly]

theorem allocatedCandidateTerminalFullInput_mass_bound
    (s m Cprimitive nTags nVars : ℕ) {x work cumulative : ℝ}
    (hx : 0 ≤ x) (hw : 0 ≤ work) (hc : 0 ≤ cumulative)
    (htags : (nTags : ℝ) ≤ x) (hvars : (nVars : ℝ) ≤ x) :
    let p := allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative
    ((nTags : ℝ) + 1) ^ s * Real.exp work *
      (actualCandidateSlowProjectionMassBudget m nVars p
        (((cumulative + ((cumulative + 2) ^ 2 + 2) ^ 63) + 2) ^ 8)) ^ s ≤
          Real.exp ((p + 2) ^ 4) := by
  obtain ⟨hp, _, hxp, hwp, hsp, hmp, hBp, _⟩ :=
    allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hw hc
  exact actualCandidateSlowProjectionMassBudget_terminal_bound s m nTags nVars hp hsp hmp
    (htags.trans hxp) (hvars.trans hxp) hwp ((terminal_affine_budget_bounds hc).2.trans hBp)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def candidatePhysicalOrdinaryBudget (pFull : ℝ) : ℝ :=
  (pFull + 4) ^ 10

theorem candidatePhysicalOrdinaryBudget_bounds {pFull : ℝ} (hp : 0 ≤ pFull) :
    0 ≤ candidatePhysicalOrdinaryBudget pFull ∧
      pFull ≤ candidatePhysicalOrdinaryBudget pFull ∧
      (2 * pFull + 3) ^ 3 + pFull ≤ candidatePhysicalOrdinaryBudget pFull ∧
      pFull + 2 + 2 * (pFull + 4) ^ 2 ≤ candidatePhysicalOrdinaryBudget pFull ∧
      3 * pFull ≤ candidatePhysicalOrdinaryBudget pFull := by
  have hfour : (pFull + 4) ^ 4 ≤ candidatePhysicalOrdinaryBudget pFull :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ pFull + 4) (by norm_num : 4 ≤ 10)
  have hpow3 : 0 ≤ pFull ^ 3 := pow_nonneg hp _
  have hpow4 : 0 ≤ pFull ^ 4 := pow_nonneg hp _
  have hmass : (2 * pFull + 3) ^ 3 + pFull ≤ (pFull + 4) ^ 4 := by
    nlinarith [sq_nonneg pFull]
  have hlip : pFull + 2 + 2 * (pFull + 4) ^ 2 ≤ (pFull + 4) ^ 4 := by
    nlinarith [sq_nonneg pFull]
  have hlinear : 3 * pFull ≤ (pFull + 4) ^ 4 := by
    nlinarith [sq_nonneg pFull]
  exact ⟨by unfold candidatePhysicalOrdinaryBudget; positivity,
    (show pFull ≤ (pFull + 4) ^ 4 by linarith only [hp, hlinear]).trans hfour,
    hmass.trans hfour, hlip.trans hfour, hlinear.trans hfour⟩

theorem candidatePhysicalOrdinaryBudget_observable {pFull pGeometry : ℝ}
    (hp : 0 ≤ pFull) (hgeometry : (pGeometry + 3) ^ 2 ≤ pFull) :
    RationalFilteredNilmanifold.nativeOptionTargetObservableBudget pGeometry ≤
      candidatePhysicalOrdinaryBudget pFull := by
  apply le_trans _ (candidatePhysicalOrdinaryBudget_bounds hp).2.2.2.1
  unfold RationalFilteredNilmanifold.nativeOptionTargetObservableBudget
  gcongr

private theorem certifiedAffine_budget_lower_arithmetic {p q : ℝ}
    (hp : 0 ≤ p) (hq : p ≤ q) :
    p ≤ 2 * p + (q + 2) ^ 10 + (q + 2) ^ 8 + 1 ∧
      (p + 2) ^ 9 ≤ 2 * p + (q + 2) ^ 10 + (q + 2) ^ 8 + 1 := by
  have hq0 : 0 ≤ q := hp.trans hq
  have hbase : p + 2 ≤ q + 2 := by linarith only [hq]
  have hpowers : (p + 2) ^ 9 ≤ (q + 2) ^ 10 :=
    (pow_le_pow_left₀ (by positivity) hbase 9).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ q + 2) (by norm_num : 9 ≤ 10))
  have hten : 0 ≤ (q + 2) ^ 10 := pow_nonneg (by positivity) _
  have height : 0 ≤ (q + 2) ^ 8 := pow_nonneg (by positivity) _
  constructor <;> linarith only [hp, hten, height, hpowers]

theorem certifiedAffineCenterBudget_primitive_bounds {p : ℝ} (hp : 0 ≤ p) :
    p ≤ certifiedAffineCenterBudget p ∧ (p + 2) ^ 9 ≤ certifiedAffineCenterBudget p := by
  have hnonneg : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 := pow_nonneg (by positivity) _
  have hq : p ≤ p + ((p + 2) ^ 2 + 2) ^ 63 := le_add_of_nonneg_right hnonneg
  simpa only [certifiedAffineCenterBudget] using certifiedAffine_budget_lower_arithmetic hp hq

theorem candidatePhysicalOrdinaryBudget_mass {pFull pAffine mass : ℝ}
    (hp : 0 ≤ pFull) (ha : 0 ≤ pAffine)
    (hcenter : certifiedAffineCenterBudget pAffine ≤ pFull)
    (hmass : Real.exp (-pFull) ≤ mass) :
    Real.exp (-candidatePhysicalOrdinaryBudget pFull) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) * mass := by
  have hcenter0 : 0 ≤ certifiedAffineCenterBudget pAffine :=
    ha.trans (certifiedAffineCenterBudget_primitive_bounds ha).1
  have hloss : (2 * certifiedAffineCenterBudget pAffine + 3) ^ 3 + pFull ≤
      candidatePhysicalOrdinaryBudget pFull := by
    apply le_trans _ (candidatePhysicalOrdinaryBudget_bounds hp).2.2.1
    gcongr
  calc
    _ ≤ Real.exp (-((2 * certifiedAffineCenterBudget pAffine + 3) ^ 3)) *
        Real.exp (-pFull) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith only [hloss]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (Real.exp_nonneg _)

theorem candidatePhysicalOrdinaryBudget_separation (s : ℕ) {pFull pAffine : ℝ}
    (hp : 0 ≤ pFull) (ha : 0 ≤ pAffine)
    (hcenter : certifiedAffineCenterBudget pAffine ≤ pFull) :
    certifiedAffineLongSideBound pAffine ≤ Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s (candidatePhysicalOrdinaryBudget pFull) pFull)) := by
  have hbase := certifiedAffineCenterBudget_primitive_bounds ha
  have hlog : 2 * (pAffine + 2) ^ 9 + pAffine ≤ candidatePhysicalOrdinaryBudget pFull := by
    have hpA := hbase.1.trans hcenter
    have hpN := hbase.2.trans hcenter
    linarith only [hpA, hpN, (candidatePhysicalOrdinaryBudget_bounds hp).2.2.2.2]
  have hordinary := (candidatePhysicalOrdinaryBudget_bounds hp).1
  have hcanonical := allocatedAffineCanonicalBudget_bounds s hordinary hp
  have hcut := candidatePrimitiveFreezingCutoff_ge_input s 1 hcanonical.nonnegative
  unfold certifiedAffineLongSideBound
  rw [← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  norm_num only [Nat.cast_ofNat]
  exact hlog.trans (hcanonical.input.trans hcut)

end Erdos3.VectorPolynomial

end

end OAI
