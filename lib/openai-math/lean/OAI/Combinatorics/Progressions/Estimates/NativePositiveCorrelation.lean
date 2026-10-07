import OAI.Combinatorics.Progressions.Estimates.NativeCrossFactorization
import OAI.Combinatorics.Progressions.Nilpotent.NiltestComplement

namespace OAI

section

namespace Erdos3.NativeVectorCorrelation

open scoped TensorProduct BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_absorb_positive {I : Type*} {degree N : ℕ} [NeZero N] {p : ℝ}
    (f : I → ZMod N → ℂ) (A : ZMod N → ℝ) (hp : 2 ≤ p)
    (hA : PositiveCyclicNiltest.{0} degree N p A)
    (W : NativeVectorCorrelation degree N p (fun i x => (A x : ℂ) * f i x)) :
    Nonempty (NativeVectorCorrelation degree N (productNiltestBudget (raisedNiltestBudget p)) f) := by
  rcases hA with @⟨L, lie, alg, s, dim, top, add, smul, t2, D, hs, T, hT, hTc, heval⟩
  let U := T.raiseStep hs
  have hpq : p ≤ raisedNiltestBudget p := le_raisedNiltestBudget p
  have hU : U.ComplexityLE (raisedNiltestBudget p) :=
    T.raiseStep_complexity hs (by linarith) hTc
  have hval (x : ZMod N) : (A x : ℂ) = star (U.evalCyclic N (fun _ => x)) := by
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.star_def, Complex.conj_re, heval]
    · simp only [Complex.ofReal_im, Complex.star_def, Complex.conj_im,
        (T.unit_interval_evalCyclic hT N (fun _ => x)).1, neg_zero]
  let W' : NativeVectorCorrelation degree N (raisedNiltestBudget p)
      (fun iu : I × Unit => fun x => f iu.1 x * star (U.evalCyclic N (fun _ => x))) := {
    L := W.L
    dim := W.dim
    model := W.model
    test := W.test
    complexity := W.complexity.mono hpq
    coordinate := (W.coordinate, ())
    correlation := by
      have h := (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans W.correlation
      simpa only [hval, mul_comm] using h }
  exact exists_absorb (D.raiseStep hs) (fun _ : Unit => U) f (hp.trans hpq) (fun _ => hU) W'

end Erdos3.NativeVectorCorrelation

end

end OAI
