import OAI.Combinatorics.Progressions.Estimates.NativeAbsorbedIntervals

namespace OAI

section

namespace Erdos3

namespace NativeDegreeRankFamily

variable {s r : ℕ} {G : Type*} [AddGroup G] {p : ℝ} (W : NativeDegreeRankFamily s r G p)

noncomputable def shiftPair (i : Fin W.outputDim) (a h : G) (δ n : ℤ) : ℂ :=
  star (W.eval i h n) * W.eval i (h - a) (n + δ)

theorem shiftPair_norm (i : Fin W.outputDim) (a h : G) (δ n : ℤ) :
    ‖W.shiftPair i a h δ n‖ ≤ 1 := by
  rw [shiftPair, norm_mul, norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval i h n)).trans
    (W.norm_eval i (h - a) (n + δ))

theorem shiftPair_mul_star (i : Fin W.outputDim) (a h k : G) (δ n : ℤ) :
    W.shiftPair i a h δ n * star (W.shiftPair i a k δ n) =
      fourPointProduct (W.eval i h) (W.eval i (h - a))
        (W.eval i k) (W.eval i (k - a)) δ n := by
  simp only [shiftPair, fourPointProduct, star_mul, star_star]
  ring

theorem quadruple_common_anchor (i : Fin W.outputDim) (a h k : G) (δ n : ℤ) (w v : ℂ) :
    fourPointProduct (W.eval i h) (W.eval i (h - a))
        (W.eval i k) (W.eval i (k - a)) δ n * w * v =
      (w * star (W.shiftPair i a k δ n)) * (W.shiftPair i a h δ n * v) := by
  rw [← W.shiftPair_mul_star]
  ring

end NativeDegreeRankFamily

namespace NativeMultilinearIntervalFamily

theorem rankProduct_eq_shiftPairs {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
    {W : NativeCorrelationStructure s r N p f} (B : NativeMultilinearIntervalFamily W q)
    (t : B.quadruples) (n : ℤ) :
    B.rankProduct t n =
      W.family.shiftPair B.rankCoordinate t.val.1 t.val.2.1 (B.delta t) n *
        star (W.family.shiftPair B.rankCoordinate t.val.1 t.val.2.2 (B.delta t) n) :=
  (W.family.shiftPair_mul_star B.rankCoordinate t.val.1 t.val.2.1 t.val.2.2 (B.delta t) n).symm

end NativeMultilinearIntervalFamily

end Erdos3

end

end OAI
