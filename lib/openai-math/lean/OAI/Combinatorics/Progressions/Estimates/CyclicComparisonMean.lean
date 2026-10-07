import OAI.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem CyclicNiltestUpperComparison.mean_le {s N : ℕ} [NeZero N] {P error : ℝ}
    {f g : ZMod N → ℝ} (h : CyclicNiltestUpperComparison.{0} s N P error f g)
    (hP : 2 ≤ P) : (𝔼 x, f x) ≤ (𝔼 x, g x) + error := by
  let D := RationalTorus.trivialNilmanifold 0
  let T := RationalFilteredNilmanifold.Niltest.const D (fun _ : Unit => 1) 1
  have hT : T.UnitIntervalValued := by intro z; norm_num [T, RationalFilteredNilmanifold.Niltest.const]
  have hTc : T.ComplexityLE P := RationalTorus.trivialNilmanifold_const_one_complexity 0 _ hP
  have htest := h D (Nat.zero_le s) T hT hTc
  have hd : (𝔼 x, (f x - g x)) ≤ error := by
    simpa only [T, RationalFilteredNilmanifold.Niltest.evalCyclic,
      RationalFilteredNilmanifold.Niltest.eval_const, Complex.one_re, mul_one] using htest
  rw [Finset.expect_sub_distrib] at hd
  linarith

theorem CyclicNiltestUpperComparison.mean_le_const {s N : ℕ} [NeZero N] {P error c : ℝ}
    {f : ZMod N → ℝ} (h : CyclicNiltestUpperComparison.{0} s N P error f (fun _ => c))
    (hP : 2 ≤ P) : (𝔼 x, f x) ≤ c + error := by
  simpa only [Fintype.expect_const] using CyclicNiltestUpperComparison.mean_le h hP

end Erdos3

end

end OAI
