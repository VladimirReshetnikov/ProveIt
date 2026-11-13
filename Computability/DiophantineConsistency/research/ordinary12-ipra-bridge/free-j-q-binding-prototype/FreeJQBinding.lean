import DiophantineConsistency.Ordinary12FreeJ
import DiophantineConsistency.Ordinary12RankAdapter
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJQBinding
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.Ordinary12RankAdapter
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem qm_binding (p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) :
    Equivalent (pairEval (core p).qm v) (natural (v 0 * ((p 0).toNat : V))) := by
  have hn : (-p 0).toNat = 0 := Int.toNat_eq_zero.mpr (neg_nonpos.mpr hbeta)
  simp [core, pairEval, Expr.splitNatural, NatExpr.evalSemiring, Equivalent, natural, hn]

theorem q_binding (p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) :
    pairEval (1+(core p).qm) v = natural (1 + v 0 * ((p 0).toNat : V)) := by
  have hn : (-p 0).toNat = 0 := Int.toNat_eq_zero.mpr (neg_nonpos.mpr hbeta)
  simp [core, pairEval, Expr.splitNatural, NatExpr.evalSemiring, natural, hn]

theorem q_positive (p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) :
    0 < (pairEval (1+(core p).qm) v).1 := by
  have hn : (-p 0).toNat = 0 := Int.toNat_eq_zero.mpr (neg_nonpos.mpr hbeta)
  simp [core, pairEval, Expr.splitNatural, NatExpr.evalSemiring, hn]

/-- The graph q is positive without any divisibility, rank or port-size bound. -/
def graphQ (p : Fin 4 → ℤ) (v : Fin 12 → V) : V :=
  (pairEval (1+(core p).qm) v).1

theorem graphQ_eq (p : Fin 4 → ℤ) (v : Fin 12 → V) (hbeta : 0 ≤ p 0) :
    graphQ p v = ((p 0).toNat : V) * v 0 + 1 := by
  have he := congrArg Prod.fst (q_binding p v hbeta)
  simpa [graphQ, natural, mul_comm, add_comm] using he

theorem graph_cancellations (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (hbeta : 0 ≤ p 0)
    (hport : ((p 0).toNat : V) = Exp.exp (590069:V)-1)
    (Y X t R : V) (hY : graphQ p v ^ 3 ∣ Y)
    (hH : graphQ p v ^ 5 ∣ (3+4*Y*(X+1))*t)
    (h3 : graphQ p v ∣ 3*Exp.exp R) :
    graphQ p v ^ 4 ∣ t ∧ graphQ p v ∣ Exp.exp R := by
  have hqpos : 0 < graphQ p v := q_positive p v hbeta
  have hq : graphQ p v = (Exp.exp (590069:V)-1) * v 0 + 1 := by
    rw [graphQ_eq p v hbeta, hport]
  exact conditional_compact44_cancellations (graphQ p v) Y X t R (v 0) hqpos hY hH hq h3

end FreeJQBinding
#print axioms FreeJQBinding.qm_binding
#print axioms FreeJQBinding.q_binding
#print axioms FreeJQBinding.q_positive
#print axioms FreeJQBinding.graphQ_eq
#print axioms FreeJQBinding.graph_cancellations
