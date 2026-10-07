import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

noncomputable def preparedRoundedRank (p : ℝ) (e : ℕ) : ℕ :=
  ⌈Real.exp ((p + 2)^e)⌉₊

theorem preparedRoundedRank_exp_le (p : ℝ) (e : ℕ) :
    Real.exp ((p + 2)^e) ≤ (preparedRoundedRank p e : ℝ) :=
  Nat.le_ceil _

theorem preparedRoundedRank_one_le (p : ℝ) (e : ℕ) :
    1 ≤ preparedRoundedRank p e := by
  have hpos := (Real.exp_pos ((p + 2)^e)).trans_le (preparedRoundedRank_exp_le p e)
  have : 0 < preparedRoundedRank p e := by exact_mod_cast hpos
  omega

theorem preparedRoundedRank_le_exp {p : ℝ} (hp : 2 ≤ p) (e : ℕ) :
    (preparedRoundedRank p e : ℝ) ≤ Real.exp ((p + 2)^(e + 1)) := by
  have hbase : 1 ≤ p + 2 := by linarith
  have hu : 1 ≤ (p + 2)^e := one_le_pow₀ hbase
  have hexp : 1 ≤ Real.exp ((p + 2)^e) := Real.one_le_exp_iff.mpr (by linarith)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hnext : (p + 2)^e + 1 ≤ (p + 2)^(e + 1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ Real.exp ((p + 2)^e) + 1 :=
      (Nat.ceil_lt_add_one (Real.exp_nonneg ((p + 2)^e))).le
    _ ≤ Real.exp ((p + 2)^e) * 2 := by linarith
    _ ≤ Real.exp ((p + 2)^e) * Real.exp 1 :=
      mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg _)
    _ = Real.exp ((p + 2)^e + 1) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hnext

theorem preparedRoundedRank_exp_requirement {p required : ℝ} {e : ℕ}
    (hrequired : required ≤ (p + 2)^e) :
    Real.exp required ≤ (preparedRoundedRank p e : ℝ) :=
  (Real.exp_le_exp.mpr hrequired).trans (preparedRoundedRank_exp_le p e)

end Erdos3

end

end OAI
