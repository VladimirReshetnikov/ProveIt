import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateThresholdSuccessor
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalTerminalReset

namespace OAI

section

namespace Erdos3.VectorPolynomial

def allocatedAffineResetHeightLog (p : ℝ) : ℝ := (p + 4) ^ 12

theorem allocatedAffineResetHeightLog_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedAffineResetHeightLog p ∧
      p ≤ allocatedAffineResetHeightLog p ∧
      (p + 4) ^ 11 ≤ allocatedAffineResetHeightLog p ∧
      (p + 3) ^ 7 ≤ allocatedAffineResetHeightLog p ∧
      (p + 2) ^ 4 ≤ allocatedAffineResetHeightLog p := by
  have hbase : 1 ≤ p + 4 := by linarith
  have hlinear : p + 4 ≤ (p + 4) ^ 12 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by norm_num : 1 ≤ 12)
  have h11 : (p + 4) ^ 11 ≤ (p + 4) ^ 12 :=
    pow_le_pow_right₀ hbase (by norm_num)
  have h7 : (p + 3) ^ 7 ≤ (p + 4) ^ 12 :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ p + 3)
      (by linarith : p + 3 ≤ p + 4) 7).trans
      (pow_le_pow_right₀ hbase (by norm_num))
  have h4 : (p + 2) ^ 4 ≤ (p + 4) ^ 12 :=
    (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
      (by linarith : p + 2 ≤ p + 4) 4).trans
      (pow_le_pow_right₀ hbase (by norm_num))
  dsimp only [allocatedAffineResetHeightLog]
  exact ⟨pow_nonneg (by linarith) _, (by linarith), h11, h7, h4⟩

theorem allocatedAffineResetHeightLog_exp_bounds {p : ℝ} (hp : 0 ≤ p) :
    1 ≤ Real.exp (allocatedAffineResetHeightLog p) ∧
      Real.exp p ≤ Real.exp (allocatedAffineResetHeightLog p) ∧
      Real.exp ((p + 4) ^ 11) ≤ Real.exp (allocatedAffineResetHeightLog p) ∧
      Real.exp ((p + 3) ^ 7) ≤ Real.exp (allocatedAffineResetHeightLog p) ∧
      Real.exp ((p + 2) ^ 4) ≤ Real.exp (allocatedAffineResetHeightLog p) := by
  obtain ⟨h0, hp', h11, h7, h4⟩ := allocatedAffineResetHeightLog_bounds hp
  exact ⟨Real.one_le_exp_iff.mpr h0, Real.exp_le_exp.mpr hp',
    Real.exp_le_exp.mpr h11, Real.exp_le_exp.mpr h7, Real.exp_le_exp.mpr h4⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

noncomputable def allocatedAffineResetRightLog (s : ℕ) (pFull : ℝ) : ℝ :=
  (pFull + allocatedEarlyAffineRightExponent (s + 1) 4) ^
    allocatedEarlyAffineRightExponent (s + 1) 4

noncomputable def allocatedAffineResetLeftLog (s : ℕ) (pFull : ℝ) : ℝ :=
  (pFull + allocatedEarlyAffineLeftExponent (s + 1) 4) ^
    allocatedEarlyAffineLeftExponent (s + 1) 4

noncomputable def allocatedAffineResetCompareLog (s : ℕ) (pNative : ℝ) : ℝ :=
  (pNative + allocatedAffineResetCompareExponent s) ^ allocatedAffineResetCompareExponent s

noncomputable def allocatedAffineResetMapBudget (s : ℕ) (p0 pFull : ℝ) : ℝ :=
  ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 + allocatedAffineResetHeightLog p0 + 1 + p0 +
    allocatedAffineResetRightLog s pFull

noncomputable def allocatedAffineCanonicalNativeBudget (s : ℕ) (p0 pFull : ℝ) : ℝ :=
  allocatedAffineResetNativeBudget s pFull (allocatedAffineResetMapBudget s p0 pFull) p0

noncomputable def allocatedAffineCanonicalBudget (s : ℕ) (p0 pFull : ℝ) : ℝ :=
  p0 + pFull + allocatedAffineResetMapBudget s p0 pFull +
    allocatedAffineCanonicalNativeBudget s p0 pFull +
    allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s p0 pFull) +
    allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull) +
    allocatedAffineResetLeftLog s pFull + (s + 2 : ℕ)

structure AllocatedAffineResetMapBudgetBounds (s : ℕ) (p0 pFull : ℝ) : Prop where
  nonnegative : 0 ≤ allocatedAffineResetMapBudget s p0 pFull
  input : p0 ≤ allocatedAffineResetMapBudget s p0 pFull
  pointwise : ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 ≤
    allocatedAffineResetMapBudget s p0 pFull
  height : allocatedAffineResetHeightLog p0 + 1 ≤ allocatedAffineResetMapBudget s p0 pFull
  denominatorLog : p0 + allocatedAffineResetRightLog s pFull ≤
    allocatedAffineResetMapBudget s p0 pFull

theorem allocatedAffineResetMapBudget_bounds (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    AllocatedAffineResetMapBudgetBounds s p0 pFull := by
  have hsection : 0 ≤ ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 :=
    hp0.trans (ordinaryImagePointwiseBudget_ge (s + 1) (s + 1) hp0)
  have hheight : 0 ≤ allocatedAffineResetHeightLog p0 := by
    unfold allocatedAffineResetHeightLog
    positivity
  have hright : 0 ≤ allocatedAffineResetRightLog s pFull := by
    unfold allocatedAffineResetRightLog
    positivity
  constructor <;> dsimp only [allocatedAffineResetMapBudget] <;> linarith

theorem allocatedAffineResetMapBudget_denominator (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) {l n : ℕ}
    (hl : (l : ℝ) ≤ Real.exp p0)
    (hn : (n : ℝ) ≤ Real.exp (allocatedAffineResetRightLog s pFull)) :
    ((l * n : ℕ) : ℝ) ≤ Real.exp (allocatedAffineResetMapBudget s p0 pFull) := by
  rw [Nat.cast_mul]
  calc
    (l : ℝ) * n ≤ Real.exp p0 * Real.exp (allocatedAffineResetRightLog s pFull) :=
      mul_le_mul hl hn (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p0 + allocatedAffineResetRightLog s pFull) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (allocatedAffineResetMapBudget_bounds s hp0 hFull).denominatorLog

theorem allocatedAffineResetLogBudget_nonnegative (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedAffineResetLogBudget s p := by
  unfold allocatedAffineResetLogBudget markedNativeLiftInput fullMarkedNativeInput
    pointwiseFastSectionInput
  positivity

structure AllocatedAffineCanonicalBudgetBounds (s : ℕ) (p0 pFull : ℝ) : Prop where
  nonnegative : 0 ≤ allocatedAffineCanonicalBudget s p0 pFull
  map_nonnegative : 0 ≤ allocatedAffineResetMapBudget s p0 pFull
  native_nonnegative : 0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  input : p0 ≤ allocatedAffineCanonicalBudget s p0 pFull
  full : pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  map : allocatedAffineResetMapBudget s p0 pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  native : allocatedAffineCanonicalNativeBudget s p0 pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  native_input : p0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  native_full : pFull ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  native_map : allocatedAffineResetMapBudget s p0 pFull ≤ allocatedAffineCanonicalNativeBudget s p0 pFull
  reset : allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
    allocatedAffineCanonicalBudget s p0 pFull
  compare : allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
    allocatedAffineCanonicalBudget s p0 pFull
  physical : allocatedAffineResetLeftLog s pFull ≤ allocatedAffineCanonicalBudget s p0 pFull
  interpolation_log : p0 + (s + 2 : ℕ) ≤ allocatedAffineCanonicalBudget s p0 pFull

theorem allocatedAffineCanonicalBudget_bounds (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    AllocatedAffineCanonicalBudgetBounds s p0 pFull := by
  have hm := allocatedAffineResetMapBudget_bounds s hp0 hFull
  obtain ⟨hn, hnf, hnm, hnq, hnl, hn4, hn3⟩ :=
    affineResetNativeBudget_bounds (allocatedEarlyAffineLeftExponent (s + 1) 4)
      hFull hm.nonnegative (q := p0)
  change 0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull at hn
  change pFull ≤ allocatedAffineCanonicalNativeBudget s p0 pFull at hnf
  change allocatedAffineResetMapBudget s p0 pFull ≤
    allocatedAffineCanonicalNativeBudget s p0 pFull at hnm
  change p0 ≤ allocatedAffineCanonicalNativeBudget s p0 pFull at hnq
  have hreset := allocatedAffineResetLogBudget_nonnegative s hn
  have hcompare : 0 ≤ allocatedAffineResetCompareLog s
      (allocatedAffineCanonicalNativeBudget s p0 pFull) := by
    unfold allocatedAffineResetCompareLog
    positivity
  have hleft : 0 ≤ allocatedAffineResetLeftLog s pFull := by
    unfold allocatedAffineResetLeftLog
    positivity
  have hs : (0 : ℝ) ≤ (s + 2 : ℕ) := Nat.cast_nonneg _
  constructor
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · exact hm.nonnegative
  · exact hn
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · exact hnq
  · exact hnf
  · exact hnm
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]
  · dsimp only [allocatedAffineCanonicalBudget]; linarith [hm.nonnegative]

structure AllocatedAffineCanonicalExpBounds (s : ℕ) (p0 pFull : ℝ) : Prop where
  map_absorption : Real.exp ((allocatedAffineResetMapBudget s p0 pFull + 2) ^ 4) ≤
    Real.exp (allocatedAffineCanonicalNativeBudget s p0 pFull)
  physical_absorption : Real.exp (allocatedAffineResetLeftLog s pFull) ≤
    Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull + 2) ^ (1 : ℕ))
  original_absorption : Real.exp p0 ≤
    Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull + 2) ^ (1 : ℕ))
  mapped_absorption : Real.exp ((allocatedAffineResetMapBudget s p0 pFull + 2) ^ 3 + p0) ≤
    Real.exp ((allocatedAffineCanonicalNativeBudget s p0 pFull + 2) ^ (1 : ℕ))
  compare_cutoff : Real.exp
      (allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull)) ≤
    Real.exp (candidatePrimitiveFreezingCutoff s 1 (allocatedAffineCanonicalBudget s p0 pFull))
  cost_cutoff : ∀ cost : ℝ, cost ≤ p0 → Real.exp cost ≤
    Real.exp (candidatePrimitiveFreezingCutoff s 1 (allocatedAffineCanonicalBudget s p0 pFull))
  interpolation : ∀ cost : ℝ, cost ≤ p0 → Real.exp cost * (s + 2 : ℕ) ≤
    Real.exp (candidatePrimitiveFreezingCutoff s 1 (allocatedAffineCanonicalBudget s p0 pFull))

theorem allocatedAffineCanonicalBudget_exp_bounds (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    AllocatedAffineCanonicalExpBounds s p0 pFull := by
  have hb := allocatedAffineCanonicalBudget_bounds s hp0 hFull
  obtain ⟨_, _, _, hm, hf, hq, hmq⟩ :=
    allocatedAffineResetNativeBudget_exp_bounds s hFull hb.map_nonnegative (q := p0)
  have hcut := candidatePrimitiveFreezingCutoff_ge_input s 1 hb.nonnegative
  refine ⟨hm, hf, hq, hmq, Real.exp_le_exp.mpr (hb.compare.trans hcut), ?_, ?_⟩
  · intro cost hcost
    exact Real.exp_le_exp.mpr ((hcost.trans hb.input).trans hcut)
  · intro cost hcost
    have hs : ((s + 2 : ℕ) : ℝ) ≤ Real.exp (s + 2 : ℕ) := by
      linarith [Real.add_one_le_exp ((s + 2 : ℕ) : ℝ)]
    calc
      Real.exp cost * (s + 2 : ℕ) ≤ Real.exp cost * Real.exp (s + 2 : ℕ) :=
        mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
      _ = Real.exp (cost + (s + 2 : ℕ)) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr
        ((add_le_add hcost le_rfl).trans (hb.interpolation_log.trans hcut))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

theorem allocatedAffineCanonicalBudget_le_diagonal (s : ℕ) {p0 pFull B : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) (hp0B : p0 ≤ B) (hFullB : pFull ≤ B) :
    allocatedAffineCanonicalBudget s p0 pFull ≤ allocatedAffineCanonicalBudget s B B := by
  have hB : 0 ≤ B := hp0.trans hp0B
  have hmap0 := (allocatedAffineResetMapBudget_bounds s hp0 hFull).nonnegative
  have hnative0 := (allocatedAffineCanonicalBudget_bounds s hp0 hFull).native_nonnegative
  have hpoint : ordinaryImagePointwiseBudget (s + 1) (s + 1) p0 ≤
      ordinaryImagePointwiseBudget (s + 1) (s + 1) B := by
    unfold ordinaryImagePointwiseBudget pointwiseFastSectionInput
    gcongr
  have hmap : allocatedAffineResetMapBudget s p0 pFull ≤
      allocatedAffineResetMapBudget s B B := by
    unfold allocatedAffineResetMapBudget allocatedAffineResetHeightLog allocatedAffineResetRightLog
    gcongr
  have hnative : allocatedAffineCanonicalNativeBudget s p0 pFull ≤
      allocatedAffineCanonicalNativeBudget s B B := by
    unfold allocatedAffineCanonicalNativeBudget allocatedAffineResetNativeBudget affineResetNativeBudget
    gcongr
  have hreset : allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
      allocatedAffineResetLogBudget s (allocatedAffineCanonicalNativeBudget s B B) := by
    unfold allocatedAffineResetLogBudget markedNativeLiftInput fullMarkedNativeInput
      pointwiseFastSectionInput
    gcongr
  have hcompare : allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s p0 pFull) ≤
      allocatedAffineResetCompareLog s (allocatedAffineCanonicalNativeBudget s B B) := by
    unfold allocatedAffineResetCompareLog
    gcongr
  have hleft : allocatedAffineResetLeftLog s pFull ≤ allocatedAffineResetLeftLog s B := by
    unfold allocatedAffineResetLeftLog
    gcongr
  unfold allocatedAffineCanonicalBudget
  linarith

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open NilpotentLieFiltration

private noncomputable def canonicalSectionPolynomial (s : ℕ) (P : Polynomial ℕ) : Polynomial ℕ :=
  2 * (P + Polynomial.C (s + 3)) ^ (s + 3) +
    ((P + Polynomial.C (s + 3)) ^ (s + 3)) ^ 2 + P

noncomputable def allocatedAffineCanonicalBudgetPolynomial (s : ℕ) : Polynomial ℕ :=
  let X := Polynomial.X
  let sectionPoly := canonicalSectionPolynomial (s + 1) X
  let right := (X + Polynomial.C (allocatedEarlyAffineRightExponent (s + 1) 4)) ^
    allocatedEarlyAffineRightExponent (s + 1) 4
  let left := (X + Polynomial.C (allocatedEarlyAffineLeftExponent (s + 1) 4)) ^
    allocatedEarlyAffineLeftExponent (s + 1) 4
  let map := sectionPoly + sectionPoly + (X + 2) ^ 5 + (X + 4) ^ 12 + 1 + X + right
  let native := X + map + X + left + (map + 2) ^ 4
  let nativeSection := canonicalSectionPolynomial (s + 1) native
  let full := (nativeSection + Polynomial.C (allocatedAffineResetFactorExponent s)) ^
      allocatedAffineResetFactorExponent s + (native + 2) ^ 1 + nativeSection
  let reset := ((full + 2) ^ 11 + full + Polynomial.C (allocatedAffineResetLiftExponent s)) ^
    allocatedAffineResetLiftExponent s
  X + X + map + native + reset +
    (native + Polynomial.C (allocatedAffineResetCompareExponent s)) ^
      allocatedAffineResetCompareExponent s + left + Polynomial.C (s + 2)

theorem allocatedAffineCanonicalBudgetPolynomial_eval (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (allocatedAffineCanonicalBudgetPolynomial s).eval₂ (Nat.castRingHom ℝ) B =
      allocatedAffineCanonicalBudget s B B := by
  simp only [allocatedAffineCanonicalBudgetPolynomial, canonicalSectionPolynomial,
    allocatedAffineCanonicalBudget, allocatedAffineResetMapBudget,
    allocatedAffineCanonicalNativeBudget, allocatedAffineResetNativeBudget,
    affineResetNativeBudget, allocatedAffineResetRightLog, allocatedAffineResetLeftLog,
    allocatedAffineResetCompareLog, allocatedAffineResetLogBudget,
    ordinaryImagePointwiseBudget, allocatedAffineResetHeightLog,
    markedNativeLiftInput, fullMarkedNativeInput, pointwiseFastSectionInput,
    max_eq_left hB, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Polynomial.eval₂_one, Nat.coe_castRingHom,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]

noncomputable def allocatedAffineCanonicalBackendPolynomial (s : ℕ) : Polynomial ℕ :=
  let P := allocatedAffineCanonicalBudgetPolynomial s
  P + 12 * (P + Polynomial.C (candidatePrimitivePhysicalBudgetExponent s 1)) ^
    candidatePrimitivePhysicalBudgetExponent s 1 + 32

theorem allocatedAffineCanonicalBackendPolynomial_eval (s : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) B =
      allocatedAffineCanonicalBudget s B B +
        finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
          (allocatedAffineCanonicalBudget s B B) := by
  simp only [allocatedAffineCanonicalBackendPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_ofNat, Nat.coe_castRingHom, allocatedAffineCanonicalBudgetPolynomial_eval s hB,
    finiteFreezingRecursiveParameter]
  ring

private theorem power_le_recursiveParameter (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    (p + C) ^ C ≤ finiteFreezingRecursiveParameter C p := by
  have hpow : 0 ≤ (p + C) ^ C := pow_nonneg (by positivity) _
  unfold finiteFreezingRecursiveParameter
  linarith only [hpow]

theorem allocatedAffineCanonical_cutoffCost_le_recursive (s : ℕ) {p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) :
    candidateSideCutoffCost
      (Real.exp (candidatePrimitiveFreezingCutoff s 1
        (allocatedAffineCanonicalBudget s p0 pFull))) ≤
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull) := by
  have hp := (allocatedAffineCanonicalBudget_bounds s hp0 hFull).nonnegative
  exact ((candidatePrimitiveFreezingCutoff_integer_cost s 1 hp).trans
    (candidatePrimitiveFreezingCutoff_add_two_le_budget s 1 hp)).trans
      (power_le_recursiveParameter _ hp)

structure AllocatedAffineCanonicalBackendBounds (s : ℕ) (p0 pFull upper : ℝ) : Prop where
  canonical : allocatedAffineCanonicalBudget s p0 pFull ≤ upper
  recursive : finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
    (allocatedAffineCanonicalBudget s p0 pFull) ≤ upper
  cutoff : candidatePrimitiveFreezingCutoff s 1
    (allocatedAffineCanonicalBudget s p0 pFull) ≤ upper
  cutoff_cost : candidateSideCutoffCost
    (Real.exp (candidatePrimitiveFreezingCutoff s 1
      (allocatedAffineCanonicalBudget s p0 pFull))) ≤ upper

theorem allocatedAffineCanonicalBackendPolynomial_bounds (s : ℕ) {p0 pFull B : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) (hp0B : p0 ≤ B) (hFullB : pFull ≤ B) :
    AllocatedAffineCanonicalBackendBounds s p0 pFull
      ((allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) B) := by
  have hB := hp0.trans hp0B
  have hp := (allocatedAffineCanonicalBudget_bounds s hp0 hFull).nonnegative
  have hd := (allocatedAffineCanonicalBudget_bounds s hB hB).nonnegative
  have hdiag := allocatedAffineCanonicalBudget_le_diagonal s hp0 hFull hp0B hFullB
  have hrec :
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull) ≤
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s B B) := by
    unfold finiteFreezingRecursiveParameter
    gcongr
  have hrec0 : 0 ≤
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s B B) := by
    unfold finiteFreezingRecursiveParameter
    positivity
  have hrecUpper :
      finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 pFull) ≤
      (allocatedAffineCanonicalBackendPolynomial s).eval₂ (Nat.castRingHom ℝ) B := by
    rw [allocatedAffineCanonicalBackendPolynomial_eval s hB]
    linarith only [hrec, hd]
  constructor
  · rw [allocatedAffineCanonicalBackendPolynomial_eval s hB]
    linarith only [hdiag, hrec0]
  · exact hrecUpper
  · exact ((candidatePrimitiveFreezingCutoff_le_budget s 1 hp).trans
      (power_le_recursiveParameter _ hp)).trans hrecUpper
  · exact (allocatedAffineCanonical_cutoffCost_le_recursive s hp0 hFull).trans hrecUpper

theorem exists_allocatedAffineCanonicalBackend_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (B p0 pFull : ℝ),
      0 ≤ p0 → 0 ≤ pFull → p0 ≤ B → pFull ≤ B →
      AllocatedAffineCanonicalBackendBounds s p0 pFull ((B + C) ^ C) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_natPolynomial_eval_budget (allocatedAffineCanonicalBackendPolynomial s)
  refine ⟨C, hC, ?_⟩
  intro B p0 pFull hp0 hFull hp0B hFullB
  have hb := allocatedAffineCanonicalBackendPolynomial_bounds s hp0 hFull hp0B hFullB
  have hpoly := hbound B (hp0.trans hp0B)
  exact ⟨hb.canonical.trans hpoly, hb.recursive.trans hpoly,
    hb.cutoff.trans hpoly, hb.cutoff_cost.trans hpoly⟩

noncomputable def allocatedAffineCanonicalBackendExponent (s : ℕ) : ℕ :=
  (exists_allocatedAffineCanonicalBackend_budget s).choose

theorem allocatedAffineCanonicalBackendExponent_ge_two (s : ℕ) :
    2 ≤ allocatedAffineCanonicalBackendExponent s :=
  (exists_allocatedAffineCanonicalBackend_budget s).choose_spec.1

theorem allocatedAffineCanonicalBackend_bounds (s : ℕ) {B p0 pFull : ℝ}
    (hp0 : 0 ≤ p0) (hFull : 0 ≤ pFull) (hp0B : p0 ≤ B) (hFullB : pFull ≤ B) :
    AllocatedAffineCanonicalBackendBounds s p0 pFull
      ((B + allocatedAffineCanonicalBackendExponent s) ^
        allocatedAffineCanonicalBackendExponent s) :=
  (exists_allocatedAffineCanonicalBackend_budget s).choose_spec.2 B p0 pFull
    hp0 hFull hp0B hFullB

end Erdos3.VectorPolynomial

end

end OAI
