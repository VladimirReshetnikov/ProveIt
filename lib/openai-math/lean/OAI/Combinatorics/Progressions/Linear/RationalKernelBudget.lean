import OAI.Combinatorics.Progressions.Dynamics.RationalHeightBudget
import OAI.Combinatorics.Progressions.Estimates.RationalSubspaces

namespace OAI

section

namespace Erdos3

theorem rationalKernelHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalKernelHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  have hsolve := rationalSolveHeight_le_budget r H hp hr hH
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfront : (2 : ℝ) * (r + 1) ≤ Real.exp (1 + (r : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul htwo (Real.add_one_le_exp r) (by positivity) (by positivity)
  have hbase : (rationalSolveHeight r H : ℝ) * H ≤
      Real.exp ((p + 2) ^ 5 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul hsolve hH (Nat.cast_nonneg _) (by positivity)
  have hpower := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hbase r
  rw [← Real.exp_nat_mul] at hpower
  have hbound : (rationalKernelHeight r H : ℝ) ≤
      Real.exp (1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p)) := by
    unfold rationalKernelHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (by positivity)
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  calc
    1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p) ≤
        1 + p + p * ((p + 2) ^ 5 + p) := by gcongr
    _ ≤ (p + 2) ^ 7 := by
      have h : 0 ≤ p ^ 7 + 13 * p ^ 6 + 74 * p ^ 5 + 240 * p ^ 4 +
          480 * p ^ 3 + 591 * p ^ 2 + 415 * p + 127 := by positivity
      nlinarith

theorem exists_rational_kernel_basis_exp_height {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℚ) {H : ℕ} (hHpos : 1 ≤ H)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hdim : (Fintype.card ι : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)))
      ℚ (LinearMap.ker A.mulVecLin), ∀ i j,
        ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤ Real.exp ((p + 2) ^ 7) ∧
        ((((b i : κ → ℚ) j).den) : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_rational_kernel_basis A hHpos hA
  have hrp : (r : ℝ) ≤ p := (show (r : ℝ) ≤ Fintype.card ι from by exact_mod_cast hr).trans hdim
  have hbudget := rationalKernelHeight_le_budget r H hp hrp hH
  refine ⟨b, fun i j => ?_⟩
  constructor
  · exact (show ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤ rationalKernelHeight r H from
      by exact_mod_cast (hb i j).1).trans hbudget
  · exact (show ((((b i : κ → ℚ) j).den) : ℝ) ≤ rationalKernelHeight r H from
      by exact_mod_cast (hb i j).2).trans hbudget

end Erdos3

end

end OAI
