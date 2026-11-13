import P86NaturalCancel
import P74PositiveGuard

/-! Source-only proposed ring and model bridge. The literal graphs and all
proofs are unelaborated; no endpoint or external byte binding is asserted. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.RingNatural86To74Draft
open AdaptiveEquationSyntax2011
variable {R : Type*} [CommRing R]

def shift (v : Fin 14 → R) : Fin 14 → R := fun j => v j+1

/-- These are the two local cancellations used in the 86-row graph. -/
theorem qF_cut (b f : R) : (1+b)-(f+1)=b-f := by ring
theorem guard_cut (g b f h : R) : g+(b-f)-b*(h+1)=g-f-b*h := by ring

/-- The four restricted factors agree after every coordinate is shifted. -/
theorem restricted_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86NaturalCancel.graph p).first.evalRing v=(P74PositiveGuard.graph p).first.evalRing (shift v) ∧
    (P86NaturalCancel.graph p).main.evalRing v=(P74PositiveGuard.graph p).main.evalRing (shift v) ∧
    (P86NaturalCancel.graph p).aux.evalRing v=(P74PositiveGuard.graph p).aux.evalRing (shift v) ∧
    (P86NaturalCancel.graph p).strong.evalRing v=(P74PositiveGuard.graph p).strong.evalRing (shift v) := by
  simp only [P86NaturalCancel.graph,P74PositiveGuard.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    shift,Int.cast_one,Nat.cast_one,qF_cut]

/-- The guard cancellation needs no input sign or port hypotheses. -/
theorem guard_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86NaturalCancel.graph p).guardFactor.evalRing v=
      (P74PositiveGuard.graph p).guardFactor.evalRing (shift v) := by
  simp only [P86NaturalCancel.graph,P74PositiveGuard.graph,Expr.evalRing_add,Expr.evalRing_sub,
    Expr.evalRing_mul,Expr.evalRing_var,Expr.evalRing_constant,Expr.evalRing_ofNat,
    shift,Int.cast_one,Nat.cast_one,qF_cut,guard_cut]

/-- Exact whole-output equality at shifted ring coordinates. -/
theorem output_eval (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86NaturalCancel.graph p).output.evalRing v=(P74PositiveGuard.graph p).output.evalRing (shift v) := by
  rw [P86NaturalCancel.output_shape,P74PositiveGuard.output_shape]
  simp only [Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_mul,
    Expr.evalRing_ofNat,Expr.evalRing_constant,Int.cast_one,Nat.cast_one]
  rcases restricted_eval p v with ⟨h0,h1,h2,h3⟩
  rw [h0,h1,h2,h3,guard_eval]

/-- Ring evaluation of the syntactic positive shift. -/
theorem positiveShift_eval (e : Expr (Fin 14)) (v : Fin 14 → R) :
    (positiveShift e).evalRing v=e.evalRing (shift v) := by
  induction e <;> simp_all [positiveShift,Expr.subst,Expr.evalRing,shift]

theorem output_eq_positiveShift (p : Fin 4 → ℤ) (v : Fin 14 → R) :
    (P86NaturalCancel.graph p).output.evalRing v=
      (positiveShift (P74PositiveGuard.graph p).output).evalRing v := by
  rw [positiveShift_eval]
  exact output_eval p v

end DiophantineConsistency.RingNatural86To74Draft

#print axioms DiophantineConsistency.RingNatural86To74Draft.output_eq_positiveShift
