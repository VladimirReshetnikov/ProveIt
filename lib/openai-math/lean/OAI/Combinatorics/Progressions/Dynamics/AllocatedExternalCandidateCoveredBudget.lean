import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateFreezingScoreBudget

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def finiteFreezingInitialPrecision (p : ℝ) : ℝ :=
  Real.exp (-((p + 2) ^ 3))

noncomputable def finiteFreezingInitialDiscard (p : ℝ) : ℝ :=
  Real.exp (-(4 * p + 8))

noncomputable def finiteFreezingRecursiveParameter (C : ℕ) (p : ℝ) : ℝ :=
  12 * (p + C) ^ C + 32

theorem finiteFreezing_initial_precision_pos (p : ℝ) :
    0 < finiteFreezingInitialPrecision p := Real.exp_pos _

theorem finiteFreezing_initial_discard_pos (p : ℝ) :
    0 < finiteFreezingInitialDiscard p := Real.exp_pos _

theorem finiteFreezing_initial_precision_lt_one {p : ℝ} (hp : 0 ≤ p) :
    finiteFreezingInitialPrecision p < 1 := by
  apply Real.exp_lt_one_iff.mpr
  have : 0 < (p + 2) ^ 3 := by positivity
  linarith

theorem finiteFreezing_initial_discard_lt_one {p : ℝ} (hp : 0 ≤ p) :
    finiteFreezingInitialDiscard p < 1 := by
  apply Real.exp_lt_one_iff.mpr
  linarith

theorem finiteFreezing_initial_precision_exponent {p : ℝ} (hp : 0 ≤ p) :
    3 * p + Real.log 8 ≤ (p + 2) ^ 3 := by
  have hlog : Real.log (8 : ℝ) ≤ 8 := Real.log_le_self (by norm_num)
  nlinarith [sq_nonneg p, pow_nonneg hp 3]

theorem finiteFreezing_initial_discard_exponent {p : ℝ} (hp : 0 ≤ p) :
    3 * p + Real.log 8 ≤ 4 * p + 8 := by
  have hlog : Real.log (8 : ℝ) ≤ 8 := Real.log_le_self (by norm_num)
  linarith

theorem finiteFreezing_initial_score_surplus
    {Bweight Bobs Lip p scoreThreshold : ℝ} (hp : 0 ≤ p)
    (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : Bweight ≤ Real.exp p) (hobs : Bobs ≤ Real.exp p)
    (hlip : Lip ≤ Real.exp p) (hscore : Real.exp (-p) ≤ scoreThreshold) :
    Real.exp (-p) / 2 + Bweight * (Lip * finiteFreezingInitialPrecision p) +
      (Bweight * Bobs) * finiteFreezingInitialDiscard p < scoreThreshold := by
  apply finiteFreezing_exp_score_surplus hBobs hLip hweight hobs hlip
  · have h := finiteFreezing_initial_precision_exponent hp
    linarith
  · have h := finiteFreezing_initial_discard_exponent hp
    linarith
  · exact hscore

theorem finiteFreezing_initial_le_polynomial {p : ℝ} (hp : 0 ≤ p)
    {C : ℕ} (hC : 2 ≤ C) : p ≤ (p + C) ^ C := by
  have hC' : (2 : ℝ) ≤ C := by exact_mod_cast hC
  have hbase : 1 ≤ p + C := by linarith
  calc
    p ≤ p + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
    _ ≤ (p + C) ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀ hbase (by omega : 1 ≤ C)

theorem finiteFreezing_uniform_recursive_exponents (k : ℕ) {p b a : ℝ}
    (hp : 0 ≤ p) {C : ℕ} (hC : 2 ≤ C)
    (hb : b ≤ (p + C) ^ C) (hk : (k : ℝ) ≤ (p + C) ^ C)
    (ha : a ≤ (p + C) ^ C) :
    (p + C) ^ C + Real.log 4 + 2 * b + Real.log (k + 1 : ℝ) + (4 * p + 8) ≤
        finiteFreezingRecursiveParameter C p ∧
      a + 2 * b ≤ finiteFreezingRecursiveParameter C p ∧
      p + Real.log 2 ≤ finiteFreezingRecursiveParameter C p := by
  have hS : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  have hpS := finiteFreezing_initial_le_polynomial hp hC
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hklog : Real.log (k + 1 : ℝ) ≤ (k : ℝ) := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < k + 1)
    linarith
  unfold finiteFreezingRecursiveParameter
  constructor
  · linarith
  constructor <;> linarith

theorem finiteFreezing_uniform_recursive_budget (k : ℕ)
    {p cost densityCost mass a b : ℝ} (hp : 0 ≤ p) {C : ℕ} (hC : 2 ≤ C)
    (hcost : cost ≤ (p + C) ^ C) (hdensity : densityCost ≤ (p + C) ^ C)
    (hb0 : 0 ≤ b) (hb : b ≤ (p + C) ^ C) (hk : (k : ℝ) ≤ (p + C) ^ C)
    (ha : a ≤ (p + C) ^ C) (hmass : Real.exp (-a) ≤ mass) :
    max cost (densityCost + Real.log
      ((4 * Real.exp b * max 1 (Real.exp b) * (k + 1 : ℝ)) /
        finiteFreezingInitialDiscard p)) ≤ finiteFreezingRecursiveParameter C p ∧
      Real.exp (-finiteFreezingRecursiveParameter C p) ≤ mass / (Real.exp b) ^ 2 ∧
      Real.exp (-finiteFreezingRecursiveParameter C p) ≤ Real.exp (-p) / 2 := by
  obtain ⟨hcostRec, hmassRec, hscoreRec⟩ :=
    finiteFreezing_uniform_recursive_exponents k hp hC hb hk ha
  refine ⟨?_, finiteFreezing_exp_recursive_mass_le hmass hmassRec,
    finiteFreezing_exp_half_score_le hscoreRec⟩
  exact (finiteFreezing_exp_cost_le k hcost hdensity hb0 (by linarith : 0 ≤ 4 * p + 8)).trans
    hcostRec

theorem exists_finiteFreezingRecursiveParameter_bound (C : ℕ) :
    ∃ C' : ℕ, 2 ≤ C' ∧ ∀ p : ℝ, 0 ≤ p →
      finiteFreezingRecursiveParameter C p ≤ (p + C') ^ C' := by
  let poly : Polynomial ℕ := 12 * (Polynomial.X + Polynomial.C C) ^ C + 32
  obtain ⟨C', hC', hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨C', hC', ?_⟩
  intro p hp
  simpa [poly, finiteFreezingRecursiveParameter, Polynomial.eval₂_pow] using hbound p hp

theorem exists_finiteFreezing_recursive_output_bound (C Cih : ℕ) :
    ∃ Cout : ℕ, 2 ≤ Cout ∧ ∀ p : ℝ, 0 ≤ p →
      (finiteFreezingRecursiveParameter C p + Cih) ^ Cih ≤ (p + Cout) ^ Cout := by
  let poly : Polynomial ℕ :=
    (12 * (Polynomial.X + Polynomial.C C) ^ C + 32 + Polynomial.C Cih) ^ Cih
  obtain ⟨Cout, hCout, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨Cout, hCout, ?_⟩
  intro p hp
  simpa [poly, finiteFreezingRecursiveParameter, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def candidateCoveredOuterParameter (A : ℕ) (p : ℝ) : ℝ :=
  (p + A) ^ A

noncomputable def candidateCoveredRightParameter (A B : ℕ) (p : ℝ) : ℝ :=
  (candidateCoveredOuterParameter A p + B) ^ B

noncomputable def candidateCoveredDictionaryParameter (A B R : ℕ) (p : ℝ) : ℝ :=
  (candidateCoveredRightParameter A B p + R) ^ R

noncomputable def candidateCoveredGeometryParameter (A B R : ℕ) (p : ℝ) : ℝ :=
  p + candidateCoveredOuterParameter A p + candidateCoveredRightParameter A B p +
    candidateCoveredDictionaryParameter A B R p + 1

noncomputable def candidateCoveredDiagramParameter (A B R Q : ℕ) (p : ℝ) : ℝ :=
  (candidateCoveredGeometryParameter A B R p + Q) ^ Q

theorem candidateCoveredGeometryParameter_bounds (A B R : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ candidateCoveredGeometryParameter A B R p ∧
      p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredOuterParameter A p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredRightParameter A B p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredDictionaryParameter A B R p ≤ candidateCoveredGeometryParameter A B R p := by
  have ho : 0 ≤ candidateCoveredOuterParameter A p := by
    unfold candidateCoveredOuterParameter
    positivity
  have hr : 0 ≤ candidateCoveredRightParameter A B p := by
    unfold candidateCoveredRightParameter
    positivity
  have hd : 0 ≤ candidateCoveredDictionaryParameter A B R p := by
    unfold candidateCoveredDictionaryParameter
    positivity
  unfold candidateCoveredGeometryParameter
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_candidateCoveredParameters_bound (A B R Q : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      candidateCoveredOuterParameter A p ≤ (p + C) ^ C ∧
      candidateCoveredGeometryParameter A B R p ≤ (p + C) ^ C ∧
      candidateCoveredDiagramParameter A B R Q p ≤ (p + C) ^ C ∧
      p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredRightParameter A B p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredDictionaryParameter A B R p ≤ candidateCoveredGeometryParameter A B R p ∧
      candidateCoveredGeometryParameter A B R p ≤ finiteFreezingRecursiveParameter C p ∧
      candidateCoveredDiagramParameter A B R Q p ≤ finiteFreezingRecursiveParameter C p := by
  let outer : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A
  let right : Polynomial ℕ := (outer + Polynomial.C B) ^ B
  let dict : Polynomial ℕ := (right + Polynomial.C R) ^ R
  let geo : Polynomial ℕ := Polynomial.X + outer + right + dict + 1
  let total : Polynomial ℕ := geo + (geo + Polynomial.C Q) ^ Q + outer
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget total
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hgeometry := candidateCoveredGeometryParameter_bounds A B R hp
  have ho : 0 ≤ candidateCoveredOuterParameter A p := by
    unfold candidateCoveredOuterParameter
    positivity
  have hg : 0 ≤ candidateCoveredGeometryParameter A B R p := by linarith [hgeometry.1]
  have hc : 0 ≤ candidateCoveredDiagramParameter A B R Q p := by
    unfold candidateCoveredDiagramParameter
    positivity
  have htotal : candidateCoveredGeometryParameter A B R p +
      candidateCoveredDiagramParameter A B R Q p + candidateCoveredOuterParameter A p ≤
        (p + C) ^ C := by
    simpa [total, geo, dict, right, outer, candidateCoveredGeometryParameter,
      candidateCoveredDiagramParameter, candidateCoveredDictionaryParameter,
      candidateCoveredRightParameter, candidateCoveredOuterParameter,
      Polynomial.eval₂_pow] using hbound p hp
  have hoBound : candidateCoveredOuterParameter A p ≤ (p + C) ^ C := by linarith
  have hgBound : candidateCoveredGeometryParameter A B R p ≤ (p + C) ^ C := by linarith
  have hcBound : candidateCoveredDiagramParameter A B R Q p ≤ (p + C) ^ C := by linarith
  have hrec : (p + C) ^ C ≤ finiteFreezingRecursiveParameter C p := by
    unfold finiteFreezingRecursiveParameter
    have : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
    linarith
  exact ⟨hoBound, hgBound, hcBound, hgeometry.2.1, hgeometry.2.2.2.1,
    hgeometry.2.2.2.2, hgBound.trans hrec, hcBound.trans hrec⟩

end Erdos3.VectorPolynomial

end

end OAI
