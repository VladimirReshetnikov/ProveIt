import OAI.Combinatorics.Progressions.Polynomial.DegreeRankNativeInverseModels

namespace OAI

section

namespace Erdos3.NativeDegreeRankDerivativeData

open scoped BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

variable {s r N : ℕ} [NeZero N] {p q : ℝ} {f : ZMod N → ℂ}
  {B : NativeCommonDerivativeModels s N p f} (W : NativeDegreeRankDerivativeData B r q)

noncomputable def toFamily (hpq : p ≤ q) : NativeDegreeRankFamily s r (ZMod N) q where
  L := B.L
  dim := B.dim
  model := B.model
  rank := W.rank
  complexity := W.complexity
  orbit h := (B.test h).orbit
  normalized := W.vertical.normalized
  outputDim := W.unit.tailDim + 1
  output_pos := by omega
  output_bound := by simpa only [Nat.cast_add, Nat.cast_one] using W.unit.dimension
  vertical := {
    observable := W.unit.observable
    unit := W.unit.unit
    norm := W.unit.norm
    lipBound := W.unit.lipBound
    lip_bound := W.unit.lip_bound
    lipschitz := W.unit.lipschitz
    frequency := W.vertical.frequency
    height := fun i => (W.vertical.height i).trans hpq
    vertical := W.rank_vertical
    integral := W.rank_integral
  }

theorem toFamily_evalCyclic (hpq : p ≤ q) (i : Fin (W.unit.tailDim + 1)) (h x : ZMod N) :
    (W.toFamily hpq).evalCyclic N i h x = (W.unit.test i h).evalCyclic N (fun _ => x) := rfl

theorem toFamily_correlation (hpq : p ≤ q) (h : ZMod N) (hh : h ∈ B.shifts) :
    Real.exp (-(p + 1)) ≤
      ‖𝔼 x, multiplicativeDerivative f h x *
        star ((W.toFamily hpq).evalCyclic N (0 : Fin (W.unit.tailDim + 1)) h x)‖ := by
  simp only [W.toFamily_evalCyclic]
  exact W.unit.test_zero_correlation h hh

end Erdos3.NativeDegreeRankDerivativeData

end

end OAI
