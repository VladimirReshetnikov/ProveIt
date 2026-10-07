import OAI.Combinatorics.Progressions.Dynamics.PreparedFiniteForwardLaterWorkBudget
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateCoveredFamilySuccessor

namespace OAI

section

namespace Erdos3.VectorPolynomial

def candidateDegreeReturnBudget (degree : ℕ) (q : ℝ) : ℝ :=
  (3 : ℝ) ^ degree * (q + 1) - 1

@[simp] theorem candidateDegreeReturnBudget_zero (q : ℝ) :
    candidateDegreeReturnBudget 0 q = q := by
  simp [candidateDegreeReturnBudget]

theorem candidateDegreeReturnBudget_succ (degree : ℕ) (q : ℝ) :
    candidateDegreeReturnBudget (degree + 1) q =
      3 * candidateDegreeReturnBudget degree q + 2 := by
  simp only [candidateDegreeReturnBudget, pow_succ]
  ring

theorem candidateDegreeReturnBudget_nonneg (degree : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ candidateDegreeReturnBudget degree q := by
  induction degree with
  | zero => simpa using hq
  | succ degree ih =>
    rw [candidateDegreeReturnBudget_succ]
    positivity

theorem candidateDegreeReturnBudget_mono (degree : ℕ) :
    Monotone (candidateDegreeReturnBudget degree) := by
  intro q r hqr
  unfold candidateDegreeReturnBudget
  have h := mul_le_mul_of_nonneg_left hqr
    (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) degree)
  linarith only [h]

theorem candidateDegreeReturnBudget_monotone_degree {q : ℝ} (hq : 0 ≤ q) :
    Monotone (fun degree => candidateDegreeReturnBudget degree q) := by
  apply monotone_nat_of_le_succ
  intro degree
  rw [candidateDegreeReturnBudget_succ]
  have h := candidateDegreeReturnBudget_nonneg degree hq
  linarith only [h]

theorem le_candidateDegreeReturnBudget (degree : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    q ≤ candidateDegreeReturnBudget degree q := by
  simpa only [candidateDegreeReturnBudget_zero] using
    candidateDegreeReturnBudget_monotone_degree hq (Nat.zero_le degree)

theorem candidateDegreeReturnBudget_bounds_sequence (a : ℕ → ℝ) {q : ℝ}
    (hzero : a 0 ≤ q) (hstep : ∀ i, a (i + 1) ≤ 3 * a i + 2) :
    ∀ i, a i ≤ candidateDegreeReturnBudget i q := by
  intro i
  induction i with
  | zero => simpa using hzero
  | succ i ih =>
    rw [candidateDegreeReturnBudget_succ]
    have h := hstep i
    linarith only [h, ih]

theorem exists_candidateDegreeReturn_nested_power_budget
    (degreeMax A : ℕ) (constants : ℕ → ℕ) (innerDepth outerDepth : ℕ)
    (Q : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x q : ℝ}, 0 ≤ x → 0 ≤ q →
      ∀ outer ≤ outerDepth, q ≤ Q.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) →
      ∀ degree ≤ degreeMax, candidateDegreeReturnBudget degree q ≤ (x + 2) ^ C := by
  let P : Polynomial ℕ := Polynomial.C (3 ^ degreeMax) * (Q + 1)
  obtain ⟨C, hC, hbound⟩ :=
    exists_candidateNestedForwardSeed_polynomial_budget A constants innerDepth outerDepth P
  refine ⟨C, hC, ?_⟩
  intro x q hx hq outer ho hqBound degree hd
  apply (candidateDegreeReturnBudget_monotone_degree hq hd).trans
  apply (candidateDegreeReturnBudget_mono degreeMax hqBound).trans
  have hp := hbound hx outer ho
  have heval : P.eval₂ (Nat.castRingHom ℝ)
      (candidateNestedForwardSeed A constants innerDepth outer x) =
      (3 : ℝ) ^ degreeMax *
        (Q.eval₂ (Nat.castRingHom ℝ)
          (candidateNestedForwardSeed A constants innerDepth outer x) + 1) := by
    change (Polynomial.C (3 ^ degreeMax) * (Q + 1)).eval₂
      (Nat.castRingHom ℝ) _ = _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_add,
      Polynomial.eval₂_one]
    simp only [map_pow, map_ofNat]
  rw [heval] at hp
  dsimp only [candidateDegreeReturnBudget]
  linarith only [hp]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

theorem exists_candidateNestedForward_polynomial_next_seed (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ)
      {x : ℝ}, C ≤ A → 1 ≤ innerDepth → 0 ≤ x →
      P.eval₂ (Nat.castRingHom ℝ)
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤
      candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_preparedFiniteForward_local_polynomial_le_later_work 1 P
  refine ⟨C, hC, ?_⟩
  intro A constants innerDepth outer x hCA hdepth hx
  let seed := candidateNestedForwardSeed A constants innerDepth outer x
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  have hzero : (0 : ℝ) ∈ Set.Icc 0 seed := ⟨le_rfl, hseed⟩
  have hsource := preparedFiniteForwardPairedSourcePrecision_nonneg A 0 constants 0 false
    hseed hzero hzero
  have hwork := (preparedFiniteForward_model_scalar_bounds A constants 0 0
    (hC.trans hCA) hseed (by simpa only [Nat.cast_zero] using hseed)).2.1
  have hseedwork := (le_preparedFiniteForwardParameter A constants 0 hseed).trans hwork
  have hfit : seed ∈ Set.Icc 0
      ((preparedFiniteForwardPairedSourcePrecision A 0 constants 0 false seed 0 0 +
        preparedFiniteForwardWork A constants 0 seed + (1 : ℕ)) ^ 1) := by
    refine ⟨hseed, ?_⟩
    simp only [Nat.cast_one, pow_one]
    linarith only [hsource, hseedwork]
  have hpoly := hbound A 0 constants innerDepth hseed hzero hzero hCA hdepth hfit
  simpa only [candidateNestedForwardSeed_succ] using hpoly

theorem exists_candidateDegreeReturn_next_seed (degree : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ)
      {x : ℝ}, C ≤ A → 1 ≤ innerDepth → 0 ≤ x →
      candidateDegreeReturnBudget degree
        (candidateNestedForwardSeed A constants innerDepth outer x) ≤
      candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  let P : Polynomial ℕ := Polynomial.C (3 ^ degree) * (Polynomial.X + 1)
  obtain ⟨C, hC, hbound⟩ := exists_candidateNestedForward_polynomial_next_seed P
  refine ⟨C, hC, ?_⟩
  intro A constants innerDepth outer x hCA hdepth hx
  have hpoly := hbound A constants innerDepth outer hCA hdepth hx
  have heval : P.eval₂ (Nat.castRingHom ℝ)
      (candidateNestedForwardSeed A constants innerDepth outer x) =
      (3 : ℝ) ^ degree * (candidateNestedForwardSeed A constants innerDepth outer x + 1) := by
    change (Polynomial.C (3 ^ degree) * (Polynomial.X + 1)).eval₂
      (Nat.castRingHom ℝ) _ = _
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_add,
      Polynomial.eval₂_X, Polynomial.eval₂_one]
    simp only [map_pow, map_ofNat]
  rw [heval] at hpoly
  dsimp only [candidateDegreeReturnBudget]
  linarith only [hpoly]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def candidateNestedDegreeNetExponent (total initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | j + 1 => RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
      (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2

@[simp] theorem candidateNestedDegreeNetExponent_zero (total initial : ℕ) :
    candidateNestedDegreeNetExponent total initial 0 = initial := rfl

@[simp] theorem candidateNestedDegreeNetExponent_succ (total initial j : ℕ) :
    candidateNestedDegreeNetExponent total initial (j + 1) =
      RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0}
        (total - (j + 1)) 1 (candidateNestedDegreeNetExponent total initial j) + 2 := rfl

noncomputable def candidateNestedDegreeConstantBound (total initial : ℕ)
    (requirement : ℕ → ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range (total + 1),
    requirement (total - j) (candidateNestedDegreeNetExponent total initial j)

theorem candidateNestedDegreeConstant_le_bound (total initial : ℕ)
    (requirement : ℕ → ℕ → ℕ) {j : ℕ} (hj : j ≤ total) :
    requirement (total - j) (candidateNestedDegreeNetExponent total initial j) ≤
      candidateNestedDegreeConstantBound total initial requirement := by
  unfold candidateNestedDegreeConstantBound
  exact Finset.single_le_sum (f := fun j =>
    requirement (total - j) (candidateNestedDegreeNetExponent total initial j))
    (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))

noncomputable def candidateNestedDegreeNetBound (total initial : ℕ) : ℕ :=
  candidateNestedDegreeConstantBound total initial (fun _ e => e)

theorem candidateNestedDegreeNetExponent_le_bound (total initial : ℕ)
    {j : ℕ} (hj : j ≤ total) :
    candidateNestedDegreeNetExponent total initial j ≤ candidateNestedDegreeNetBound total initial :=
  candidateNestedDegreeConstant_le_bound total initial (fun _ e => e) hj

theorem exists_candidateNestedDegreeReturn_power_budget
    (total A : ℕ) (constants : ℕ → ℕ) (innerDepth : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {x : ℝ}, 0 ≤ x →
      candidateDegreeReturnBudget total
        (candidateNestedForwardSeed A constants innerDepth (2 * total) x) ≤ (x + 2) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_candidateDegreeReturn_nested_power_budget
    total A constants innerDepth (2 * total) Polynomial.X
  refine ⟨C, hC, ?_⟩
  intro x hx
  apply hbound hx
    (candidateNestedForwardSeed_nonneg A constants innerDepth (2 * total) hx)
    (2 * total) le_rfl _ total le_rfl
  simp only [Polynomial.eval₂_X, le_refl]

end Erdos3.VectorPolynomial

end

end OAI
