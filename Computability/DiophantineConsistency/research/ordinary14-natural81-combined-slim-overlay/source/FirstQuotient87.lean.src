import GuardGap87
import FirstFields86
import QuotientFacts

/-! Source-only q-cubed first quotient from the 87 own-zero. Draft graph
imports are unelaborated; no 86 zero, exact index or endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FirstQuotient87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing DirectFirstRootModelDraft
open FirstFields86Draft QCubeQuotientFactsDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 86 and 87 literal first expressions are identical; this does not
identify their guard fields or outputs. -/
theorem shared_first (p : Fin 4 → ℤ) :
    (P87ShiftedGuard.graph p).A0=(P86ResidueGraph.graph p).A0 := by rfl

/-- Extract only the first residual from the 87 graph's own zero. -/
theorem first_of_zero (p : Fin 4 → ℤ) (v : Fin 14 → V)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    eval (P86ResidueGraph.graph p).A0 v=0 := by
  rw [internalZero_iff,P87ShiftedGuard.output_shape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one] at hz
  have hfive : fiveSquares (eval (P87ShiftedGuard.graph p).A0 v)
      (eval (P87ShiftedGuard.graph p).A1 v) (eval (P87ShiftedGuard.graph p).aux v-1)
      (eval (P87ShiftedGuard.graph p).gap v) (eval (P87ShiftedGuard.graph p).guardResidual v)=0 := by
    simpa only [fiveSquares,eval] using hz
  have hf := ((fiveSquares_eq_zero_iff _ _ _ _ _).mp hfive).1
  rw [shared_first p] at hf
  exact hf

/-- Positive 87 own-zero first norm gives positive s,tau with Y=q³*s and
 tau²=D, without assuming a sign or any 86 graph zero. -/
theorem quotient_and_root (p : Fin 4 → ℤ) (beta : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hJ : 0<v 0) (hY : 0<v 7)
    (hport : (p 0 : DiffRing V)=ι beta)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    ∃ s tau : V, 0<s ∧ v 7=Q beta v*s ∧ 0<tau ∧ tau*tau=radicand v := by
  have hb : 0<b beta v := by dsimp [b]; exact mul_pos hJ hbeta
  have hD : 0<radicand v := by dsimp [radicand]; simp
  have hf := first_of_zero p v hz
  rw [first_eval p beta v hport] at hf
  have hfield := sub_eq_zero.mp hf
  simpa only [q,Q,b,M] using
    QCubeQuotientFactsDraft.quotient_and_root (b beta v) (v 7) (firstP v) (v 8)
      (radicand v) hb hY hD (by simpa only [q,Q,b,M] using hfield)

end DiophantineConsistency.FirstQuotient87Draft

#print axioms DiophantineConsistency.FirstQuotient87Draft.quotient_and_root
