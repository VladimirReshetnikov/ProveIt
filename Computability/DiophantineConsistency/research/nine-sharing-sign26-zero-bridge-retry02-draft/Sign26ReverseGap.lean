import DiophantineConsistency.Sign26ForwardBridge

/-! SOURCE-ONLY: recover the embedded gap before specializing the vector. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26ZeroBridge
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem reverseGap (p : Fin 4 → ℤ) (v : Fin 27 → V) (gap : V)
    (hz : InternalZero (Sign26CongruenceCuts.oldGap p) (Sign26CongruenceCuts.lift gap v)) :
    ι gap = Sign26CongruenceCuts.ringGap p v := by
  have h := (internalZero_iff _ _).mp hz
  simp only [Sign26CongruenceCuts.oldGap, Sign26CongruenceCuts.lift, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, Int.cast_one] at h
  simpa [Sign26CongruenceCuts.ringGap] using (sub_eq_zero.mp h)
end DiophantineConsistency.Sign26ZeroBridge
#print axioms DiophantineConsistency.Sign26ZeroBridge.reverseGap
