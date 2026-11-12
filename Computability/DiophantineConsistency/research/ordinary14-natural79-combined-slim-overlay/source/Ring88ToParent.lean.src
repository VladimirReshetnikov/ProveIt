import P88QuotientGuardedGraph
import P88FourSquareGraph

/-! Source-only 14→13 graph field cuts for a fresh parent root. No positive
witness, zero transport, Lean elaboration or endpoint is claimed. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Ring88ToParentDraft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

/-- Drop slot 13 and install an arbitrary new parent root at slot 8. -/
def project (v : Fin 14 → R) (r : R) : Fin 13 → R :=
  Function.update (fun j : Fin 13 => v j.castSucc) 8 r

def b (p : Fin 4 → ℤ) (v : Fin 14 → R) : R := v 0*(p 0 : R)
def q (p : Fin 4 → ℤ) (v : Fin 14 → R) : R := 1+b p v
def q3 (p : Fin 4 → ℤ) (v : Fin 14 → R) : R := q p v*(q p v*q p v)
def scale (p : Fin 4 → ℤ) (v : Fin 14 → R) : R := q3 p v*b p v
def k (v : Fin 14 → R) : R := v 9+v 10
def ell (v : Fin 14 → R) : R := (v 6*v 7)*(v 7*k v)
def delta (v : Fin 14 → R) : R := 1+ell v*(ell v+k v)

theorem main_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) (r : R) :
    (P88FourSquare.graph p).A1.evalRing (project v r) =
      (P88QuotientGuarded.graph p).A1.evalRing v := by
  simp [P88FourSquare.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    project,Function.update] <;> ring

theorem aux_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) (r : R) :
    (P88FourSquare.graph p).aux.evalRing (project v r) =
      (P88QuotientGuarded.graph p).aux.evalRing v := by
  simp [P88FourSquare.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    project,Function.update] <;> ring

theorem strong_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) (r : R) :
    (P88FourSquare.graph p).gap.evalRing (project v r) =
      (P88QuotientGuarded.graph p).gap.evalRing v := by
  simp [P88FourSquare.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    project,Function.update] <;> ring

/-- The parent first residual is the square of its explicitly folded Z. -/
theorem first_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) (r : R) :
    (P88FourSquare.graph p).A0.evalRing (project v r) =
      (scale p v*(ell v+k v+r-k v*(P88QuotientGuarded.graph p).Bt.evalRing v)+
        v 7*b p v-q3 p v*(P88QuotientGuarded.graph p).Bt.evalRing v)^2-
        (scale p v)^2*delta v := by
  simp [P88FourSquare.graph,P88QuotientGuarded.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    project,Function.update,scale,q3,q,b,k,ell,delta,pow_two] <;> ring

/-- Fresh-root algebra, stated over arbitrary commutative rings. -/
theorem first_cut (q3 b Y ell k t s tau r : R)
    (hY : Y=q3*s) (hr : r+(ell+k+s)=k*(b*t)+t+tau) :
    (q3*b)*(ell+k+r-k*(b*t))+Y*b-q3*(b*t)=(q3*b)*tau := by
  rw [hY]
  calc
    _=(q3*b)*((r+(ell+k+s))-(k*(b*t)+t)) := by ring
    _=(q3*b)*tau := by rw [hr]; ring

end DiophantineConsistency.Ring88ToParentDraft

#print axioms DiophantineConsistency.Ring88ToParentDraft.first_cut
