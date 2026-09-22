import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Module

/-!
# Normalized resolvents and projection flags of rate matrices

This file proves the exact finite algebra behind `markov:lem:resolvent`,
`markov:thm:flag-realization` and `markov:lem:completion` in
`docs/surreal/markov-generators-at-every-scale/article.tex`, over an arbitrary
field. The normalized resolvent of a square matrix `L` is `R_L(s) = s(sI + L)⁻¹`.

* `markov:eq:resolvent-identity`: `R_L(s)R_L(u) = (uR_L(s) - sR_L(u))/(u - s)`, and
  resolvents at different parameters commute.
* `markov:thm:flag-realization`: for a flag `P_0 = I, P_1, …, P_m` of matrices with
  `P_iP_j = P_{max(i,j)}`, the matrix `H = ∑ τ_j(P_{j-1} - P_j)` has normalized
  resolvent exactly `P_m + ∑ s/(s + τ_j)(P_{j-1} - P_j)`. Stochastic flags give
  zero row sums, and the Abel-summed form `markov:eq:inverse-signs` shows that every
  off-diagonal entry is nonpositive when the flag is entrywise nonnegative and
  `τ_1 > ⋯ > τ_m > 0`. In a real Hahn field, `τ_j = t^{α_j}` with increasing
  `α_j` satisfies exactly these order hypotheses.
* `markov:lem:completion`: adding `ε(I - 𝟙ν)` for a probability row `ν` gives the exact
  rank-one resolvent formula `markov:eq:completion-convex`, with no commutation of
  `𝟙ν` and `H`, and strictly negative off-diagonal entries.

Residue computations at prescribed Hahn scales are separate obligations.
-/

namespace Surreal.Markov

open Matrix Finset

noncomputable section

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The normalized resolvent `R_L(s) = s(sI + L)⁻¹`. -/
def resolvent (L : Matrix n n K) (s : K) : Matrix n n K :=
  s • (s • (1 : Matrix n n K) + L)⁻¹

/-- The unnormalized resolvent identity. -/
theorem inv_sub_inv {L : Matrix n n K} {s u : K} (hs : IsUnit (s • (1 : Matrix n n K) + L).det)
    (hu : IsUnit (u • (1 : Matrix n n K) + L).det) :
    (s • (1 : Matrix n n K) + L)⁻¹ - (u • (1 : Matrix n n K) + L)⁻¹ =
      (u - s) • ((s • (1 : Matrix n n K) + L)⁻¹ * (u • (1 : Matrix n n K) + L)⁻¹) := by
  set A := s • (1 : Matrix n n K) + L
  set B := u • (1 : Matrix n n K) + L
  have hBA : B = (u - s) • (1 : Matrix n n K) + A := by
    simp only [A, B, sub_smul]
    abel
  have key : A⁻¹ * B * B⁻¹ = A⁻¹ := by
    rw [Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.mul_one]
  rw [hBA, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, nonsing_inv_mul _ hs,
    Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, ← hBA] at key
  exact (eq_sub_of_add_eq key).symm

/-- `markov:eq:resolvent-identity` in multiplied-out form. -/
theorem resolvent_mul_resolvent {L : Matrix n n K} {s u : K}
    (hs : IsUnit (s • (1 : Matrix n n K) + L).det)
    (hu : IsUnit (u • (1 : Matrix n n K) + L).det) :
    (u - s) • (resolvent L s * resolvent L u) = u • resolvent L s - s • resolvent L u := by
  have h := inv_sub_inv hs hu
  simp only [resolvent, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (u - s), ← smul_smul, ← h, smul_sub, mul_comm s u]

/-- `markov:eq:resolvent-identity`: `R_L(s)R_L(u) = (uR_L(s) - sR_L(u))/(u - s)`. -/
theorem resolvent_mul_resolvent_eq {L : Matrix n n K} {s u : K} (hsu : s ≠ u)
    (hs : IsUnit (s • (1 : Matrix n n K) + L).det)
    (hu : IsUnit (u • (1 : Matrix n n K) + L).det) :
    resolvent L s * resolvent L u = (u - s)⁻¹ • (u • resolvent L s - s • resolvent L u) := by
  rw [← resolvent_mul_resolvent hs hu, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hsu.symm),
    one_smul]

/-- Resolvents at different parameters commute. -/
theorem resolvent_commute {L : Matrix n n K} {s u : K}
    (hs : IsUnit (s • (1 : Matrix n n K) + L).det)
    (hu : IsUnit (u • (1 : Matrix n n K) + L).det) :
    resolvent L s * resolvent L u = resolvent L u * resolvent L s := by
  by_cases hsu : s = u
  · rw [hsu]
  rw [resolvent_mul_resolvent_eq hsu hs hu, resolvent_mul_resolvent_eq (Ne.symm hsu) hu hs,
    ← neg_sub u s, inv_neg, neg_smul, ← smul_neg, neg_sub]

/-- An explicit right inverse computes the normalized resolvent. -/
theorem resolvent_eq_of_mul_eq {L X : Matrix n n K} {s : K} (hs : s ≠ 0)
    (h : (s • (1 : Matrix n n K) + L) * X = s • (1 : Matrix n n K)) : resolvent L s = X := by
  have hinv : (s • (1 : Matrix n n K) + L) * (s⁻¹ • X) = 1 := by
    rw [Matrix.mul_smul, h, smul_smul, inv_mul_cancel₀ hs, one_smul]
  rw [resolvent, inv_eq_right_inv hinv, smul_smul, mul_inv_cancel₀ hs, one_smul]

section Flag

variable (P : ℕ → Matrix n n K) (τ : ℕ → K) (m : ℕ)

/-- The flag increments `E_j = P_j - P_{j+1}`; indices are shifted by one from
the source, so `τ j` is the source's `τ_{j+1}`. -/
def flagStep (j : ℕ) : Matrix n n K :=
  P j - P (j + 1)

/-- `markov:eq:simple-inverse`: the generator `H = ∑ τ_j(P_{j-1} - P_j)`. -/
def flagGenerator : Matrix n n K :=
  ∑ j ∈ range m, τ j • flagStep P j

/-- `markov:eq:simple-inverse-resolvent`: the claimed resolvent. -/
def flagResolvent (s : K) : Matrix n n K :=
  P m + ∑ j ∈ range m, (s / (s + τ j)) • flagStep P j

variable {P m}

/-- The flag relations `P_iP_j = P_{max(i,j)}` up to `m`. -/
def IsFlag (P : ℕ → Matrix n n K) (m : ℕ) : Prop :=
  P 0 = 1 ∧ ∀ i j, i ≤ m → j ≤ m → P i * P j = P (max i j)

theorem flagStep_mul_flagStep (hP : IsFlag P m) {i j : ℕ} (hi : i < m) (hj : j < m) :
    flagStep P i * flagStep P j = if i = j then flagStep P j else 0 := by
  have h := hP.2
  simp only [flagStep, Matrix.sub_mul, Matrix.mul_sub]
  rw [h i j (by omega) (by omega), h i (j + 1) (by omega) (by omega),
    h (i + 1) j (by omega) (by omega), h (i + 1) (j + 1) (by omega) (by omega)]
  split_ifs with hij
  · subst hij
    simp only [max_self, le_add_iff_nonneg_right, zero_le, max_eq_right, max_eq_left]
    abel
  · rcases lt_or_gt_of_ne hij with hlt | hlt
    · rw [max_eq_right hlt.le, max_eq_right (by omega : i ≤ j + 1),
        max_eq_right (by omega : i + 1 ≤ j), max_eq_right (by omega : i + 1 ≤ j + 1)]
      abel
    · rw [max_eq_left hlt.le, max_eq_left (by omega : j + 1 ≤ i),
        max_eq_left (by omega : j ≤ i + 1), max_eq_left (by omega : j + 1 ≤ i + 1)]
      abel

theorem flagStep_mul_last (hP : IsFlag P m) {j : ℕ} (hj : j < m) :
    flagStep P j * P m = 0 := by
  rw [flagStep, Matrix.sub_mul, hP.2 j m (by omega) le_rfl, hP.2 (j + 1) m (by omega) le_rfl,
    max_eq_right hj.le, max_eq_right (by omega), sub_self]

/-- The increments and the last projection resolve the identity. -/
theorem last_add_sum_flagStep (hP : IsFlag P m) :
    P m + ∑ j ∈ range m, flagStep P j = 1 := by
  rw [← hP.1]
  simp only [flagStep]
  rw [Finset.sum_range_sub' P m]
  abel

/-- `markov:thm:flag-realization`: the normalized resolvent of the flag generator is exactly
`markov:eq:simple-inverse-resolvent`, for every `s` with `s ≠ 0` and `s + τ_j ≠ 0`. -/
theorem resolvent_flagGenerator (hP : IsFlag P m) {s : K} (hs : s ≠ 0)
    (hτ : ∀ j < m, s + τ j ≠ 0) :
    resolvent (flagGenerator P τ m) s = flagResolvent P τ m s := by
  apply resolvent_eq_of_mul_eq hs
  have hprod : ∀ j ∈ range m, flagGenerator P τ m * flagStep P j = τ j • flagStep P j := by
    intro j hj
    rw [flagGenerator, Finset.sum_mul]
    simp_rw [Matrix.smul_mul]
    rw [Finset.sum_eq_single j]
    · rw [flagStep_mul_flagStep hP (mem_range.mp hj) (mem_range.mp hj), if_pos rfl]
    · intro i hi hij
      rw [flagStep_mul_flagStep hP (mem_range.mp hi) (mem_range.mp hj), if_neg hij, smul_zero]
    · exact fun h => absurd hj h
  have hlast : flagGenerator P τ m * P m = 0 := by
    rw [flagGenerator, Finset.sum_mul]
    exact Finset.sum_eq_zero fun j hj => by
      rw [Matrix.smul_mul, flagStep_mul_last hP (mem_range.mp hj), smul_zero]
  have hcoef : ∀ j ∈ range m, s • ((s / (s + τ j)) • flagStep P j) +
      (s / (s + τ j)) • (τ j • flagStep P j) = s • flagStep P j := by
    intro j hj
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    calc s * (s / (s + τ j)) + s / (s + τ j) * τ j = (s + τ j) * (s / (s + τ j)) := by ring
      _ = s := mul_div_cancel₀ _ (hτ j (mem_range.mp hj))
  have hH : flagGenerator P τ m * ∑ j ∈ range m, (s / (s + τ j)) • flagStep P j =
      ∑ j ∈ range m, (s / (s + τ j)) • (τ j • flagStep P j) := by
    rw [Matrix.mul_sum]
    exact Finset.sum_congr rfl fun j hj => by rw [Matrix.mul_smul, hprod j hj]
  rw [flagResolvent, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hlast, zero_add, hH,
    Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.one_mul, Finset.smul_sum,
    add_assoc, ← Finset.sum_add_distrib, Finset.sum_congr rfl hcoef, ← Finset.smul_sum,
    ← smul_add, last_add_sum_flagStep hP]

/-- `markov:eq:inverse-signs`: Abel summation of the flag generator. -/
theorem flagGenerator_eq_abel (hP : IsFlag P m) (hm : 0 < m) :
    flagGenerator P τ m = τ 0 • (1 : Matrix n n K) +
      ∑ j ∈ range (m - 1), (τ (j + 1) - τ j) • P (j + 1) - τ (m - 1) • P m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero =>
    simp [flagGenerator, flagStep, hP.1, smul_sub]
  | succ k ih =>
    have hP' : IsFlag P (k + 1) := ⟨hP.1, fun i j hi hj => hP.2 i j (by omega) (by omega)⟩
    rw [flagGenerator, Finset.sum_range_succ, ← flagGenerator, ih hP' (by omega),
      Finset.sum_range_succ, flagStep]
    simp only [sub_smul, smul_sub]
    abel

omit [DecidableEq n] in
/-- A flag of row-stochastic matrices gives a generator with zero row sums. -/
theorem flagGenerator_mulVec_one (hstoch : ∀ j ≤ m, P j *ᵥ (fun _ => (1 : K)) = fun _ => 1) :
    flagGenerator P τ m *ᵥ (fun _ => (1 : K)) = 0 := by
  rw [flagGenerator, Matrix.sum_mulVec]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [Matrix.smul_mulVec, flagStep, Matrix.sub_mulVec, hstoch j (by simp at hj; omega),
    hstoch (j + 1) (by simp at hj; omega), sub_self, smul_zero]

/-- `markov:thm:flag-realization`: with an entrywise nonnegative flag and
`τ_1 > ⋯ > τ_m > 0`, every off-diagonal entry of the generator is nonpositive. -/
theorem flagGenerator_offDiag_nonpos [LinearOrder K] [IsStrictOrderedRing K] (hP : IsFlag P m)
    (hm : 0 < m) (hnonneg : ∀ j ≤ m, ∀ a b, 0 ≤ P j a b)
    (hanti : ∀ j, j + 1 < m → τ (j + 1) < τ j) (hpos : 0 < τ (m - 1)) {a b : n} (hab : a ≠ b) :
    flagGenerator P τ m a b ≤ 0 := by
  rw [flagGenerator_eq_abel τ hP hm]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply,
    one_apply_ne hab, smul_eq_mul, mul_zero, zero_add]
  have hsum : ∑ j ∈ range (m - 1), (τ (j + 1) - τ j) * P (j + 1) a b ≤ 0 :=
    Finset.sum_nonpos fun j hj => mul_nonpos_of_nonpos_of_nonneg
      (sub_nonpos.mpr (hanti j (by simp at hj; omega)).le) (hnonneg (j + 1) (by
        simp at hj; omega) a b)
  have hlast : 0 ≤ τ (m - 1) * P m a b := mul_nonneg hpos.le (hnonneg m le_rfl a b)
  linarith

end Flag

section Completion

/-- The rank-one matrix `𝟙ν`. -/
def onesRow (ν : n → K) : Matrix n n K :=
  Matrix.of fun _ b => ν b

omit [DecidableEq n] in
theorem onesRow_mul_onesRow {ν : n → K} (hν : ∑ b, ν b = 1) :
    onesRow ν * onesRow ν = onesRow ν := by
  ext a b
  simp [onesRow, mul_apply, ← Finset.sum_mul, hν]

omit [DecidableEq n] in
theorem mul_onesRow {H : Matrix n n K} (hH : H *ᵥ (fun _ => (1 : K)) = 0) (ν : n → K) :
    H * onesRow ν = 0 := by
  ext a b
  have := congrFun hH a
  simp only [mulVec, dotProduct, mul_one, Pi.zero_apply] at this
  simp [onesRow, mul_apply, ← Finset.sum_mul, this]

/-- `markov:eq:completion-exact` and `markov:eq:completion-convex`: for a zero-row-sum `H`, a
probability row `ν`, and `L = H + ε(I - 𝟙ν)`,
`R_L(s) = (s/(s + ε) I + ε/(s + ε) 𝟙ν) R_H(s + ε)`. -/
theorem resolvent_completion {H : Matrix n n K} (hH : H *ᵥ (fun _ => (1 : K)) = 0)
    {ν : n → K} (hν : ∑ b, ν b = 1) {s ε : K} (hs : s ≠ 0) (hsε : s + ε ≠ 0)
    (hM : IsUnit ((s + ε) • (1 : Matrix n n K) + H).det) :
    resolvent (H + ε • (1 - onesRow ν)) s =
      ((s / (s + ε)) • (1 : Matrix n n K) + (ε / (s + ε)) • onesRow ν) *
        resolvent H (s + ε) := by
  set M := (s + ε) • (1 : Matrix n n K) + H with hMdef
  set J := onesRow ν
  have hJJ : J * J = J := onesRow_mul_onesRow hν
  have hMJ : M * J = (s + ε) • J := by
    rw [hMdef, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, mul_onesRow hH, add_zero]
  apply resolvent_eq_of_mul_eq hs
  have hsum : s • (1 : Matrix n n K) + (H + ε • (1 - J)) = M - ε • J := by
    rw [hMdef, add_smul, smul_sub]
    abel
  have hR : resolvent H (s + ε) = (s + ε) • M⁻¹ := rfl
  have hprod : (M - ε • J) * (s • (1 : Matrix n n K) + ε • J) = s • M := by
    simp only [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      hMJ, hJJ]
    module
  rw [hsum, hR, Matrix.mul_smul, ← Matrix.smul_mul, smul_add, smul_smul, smul_smul,
    mul_div_cancel₀ _ hsε, mul_div_cancel₀ _ hsε, ← Matrix.mul_assoc, hprod, Matrix.smul_mul,
    mul_nonsing_inv _ hM]

omit [Fintype n] in
/-- `markov:lem:completion`: the completed generator has strictly negative off-diagonal
entries when `H` has nonpositive ones, `ε > 0` and `ν` is strictly positive. -/
theorem completion_offDiag_neg [LinearOrder K] [IsStrictOrderedRing K] {H : Matrix n n K}
    {ν : n → K} {ε : K} (hε : 0 < ε) (hν : ∀ b, 0 < ν b)
    (hH : ∀ a b, a ≠ b → H a b ≤ 0) {a b : n} (hab : a ≠ b) :
    (H + ε • (1 - onesRow ν)) a b < 0 := by
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, one_apply_ne hab, onesRow,
    of_apply, zero_sub, smul_eq_mul, mul_neg]
  linarith [hH a b hab, mul_pos hε (hν b)]

end Completion

end

end Surreal.Markov
