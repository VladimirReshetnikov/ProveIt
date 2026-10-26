import DiophantineConsistency.Representation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
/-! Extracted-source harness. Literal source definitions from the pinned repository,
not a replay of the complete Jones/Hilbert-tenth dependency chain. -/
namespace Jones1982.Nine
structure Vars where
  (R N b g G h s w φ i j : ℤ)

namespace Vars

variable (v : Vars)

def U : ℤ := v.N ^ 2 * v.w
def Y : ℤ := v.N ^ 2 * v.s
def M : ℤ := v.R * v.Y
def P : ℤ := 2 * v.M ^ 2 * v.U
def K : ℤ := v.R + 1 + v.h * (v.P - 1)
def A : ℤ := v.M * (v.U + 1)
def B' : ℤ := 2 * v.R + 1
def W : ℤ := v.b * v.w
def C : ℤ := v.B' + v.W + v.φ
def J : ℤ := 4 * v.A - 5
def Q : ℤ := 3 * v.W * v.C - 2 * (v.W ^ 2 - 1)
def D : ℤ := (v.A ^ 2 - 1) * v.C ^ 2 + 1
def E : ℤ := v.i * v.J * v.D * v.C ^ 2
def F : ℤ := (v.A ^ 2 - 1) * v.E ^ 2 + 1
def Gp : ℤ := v.A + v.F * (v.C * v.D + 1 - v.A)
def H : ℤ := v.B' + v.j * v.C
def I : ℤ := (v.Gp ^ 2 - 1) * v.H ^ 2 + 1


end Vars
/-- The two radicands. -/
def rad (V : Vars) : Fin 2 → ℤ := ![(V.P ^ 2 - 1) * V.K ^ 2 + 1, V.D * V.F * V.I]

/-- Their weights. -/
def wt (V : Vars) : Fin 2 → ℤ := fun k => rad V k ^ 2 + 2

/-- The divisor, dividend and margin. -/
def dvsr (V : Vars) : ℤ := (V.J * V.F) ^ 2
def dvnd (V : Vars) : ℤ := (V.Q * V.F + V.J * (V.H - V.C)) ^ 2
def marg (V : Vars) : ℤ := V.K ^ 2 * V.G - 4 * (V.C - V.K * V.Y) ^ 2 * V.G - 8 * V.g * V.K ^ 2


end Jones1982.Nine
namespace DiophantineConsistency.NinePolynomial
structure RingVars (A : Type*) where
  (R N b g G h s w φ i j : A)

namespace RingVars

variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 5] [OfNat R 8]
  (v : RingVars R)

def U : R := v.N ^ 2 * v.w
def Y : R := v.N ^ 2 * v.s
def M : R := v.R * v.Y
def P : R := 2 * v.M ^ 2 * v.U
def K : R := v.R + 1 + v.h * (v.P - 1)
def A : R := v.M * (v.U + 1)
def B' : R := 2 * v.R + 1
def W : R := v.b * v.w
def C : R := v.B' + v.W + v.φ
def J : R := 4 * v.A - 5
def Q : R := 3 * v.W * v.C - 2 * (v.W ^ 2 - 1)
def D : R := (v.A ^ 2 - 1) * v.C ^ 2 + 1
def E : R := v.i * v.J * v.D * v.C ^ 2
def F : R := (v.A ^ 2 - 1) * v.E ^ 2 + 1
def Gp : R := v.A + v.F * (v.C * v.D + 1 - v.A)
def H : R := v.B' + v.j * v.C
def I : R := (v.Gp ^ 2 - 1) * v.H ^ 2 + 1

def rad : Fin 2 → R := ![(v.P ^ 2 - 1) * v.K ^ 2 + 1, v.D * v.F * v.I]
def wt : Fin 2 → R := fun k => v.rad k ^ 2 + 2
def dvsr : R := (v.J * v.F) ^ 2
def dvnd : R := (v.Q * v.F + v.J * (v.H - v.C)) ^ 2
def marg : R := v.K ^ 2 * v.G - 4 * (v.C - v.K * v.Y) ^ 2 * v.G - 8 * v.g * v.K ^ 2

end RingVars


end DiophantineConsistency.NinePolynomial
namespace DiophantineConsistency.JonesSyntax
open NinePolynomial
def evalExprVars {σ : Type*} (a : σ → ℤ) (v : RingVars (Expr σ)) : Jones1982.Nine.Vars :=
  ⟨v.R.eval a, v.N.eval a, v.b.eval a, v.g.eval a, v.G.eval a,
    v.h.eval a, v.s.eval a, v.w.eval a, v.φ.eval a, v.i.eval a, v.j.eval a⟩

theorem eval_rad {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) (k : Fin 2) :
    (fun e : Expr σ => e.eval a) (v.rad k) = Jones1982.Nine.rad (evalExprVars a v) k := by
  fin_cases k <;>
    simp [Expr.eval, RingVars.rad, Jones1982.Nine.rad, evalExprVars,
      RingVars.U, RingVars.Y, RingVars.M, RingVars.P, RingVars.K,
      RingVars.A, RingVars.B', RingVars.W, RingVars.C, RingVars.J,
      RingVars.D, RingVars.E, RingVars.F, RingVars.Gp,
      RingVars.H, RingVars.I,
      Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
      Jones1982.Nine.Vars.P, Jones1982.Nine.Vars.K, Jones1982.Nine.Vars.A,
      Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W, Jones1982.Nine.Vars.C,
      Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.D,
      Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F, Jones1982.Nine.Vars.Gp,
      Jones1982.Nine.Vars.H, Jones1982.Nine.Vars.I]

theorem eval_wt {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) (k : Fin 2) :
    (v.wt k).eval a = Jones1982.Nine.wt (evalExprVars a v) k := by
  simp [RingVars.wt, Jones1982.Nine.wt, Expr.eval_pow, eval_rad, Expr.eval]

theorem eval_dvsr {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) :
    (fun e : Expr σ => e.eval a) v.dvsr = Jones1982.Nine.dvsr (evalExprVars a v) := by
  simp [Expr.eval, RingVars.dvsr, Jones1982.Nine.dvsr, evalExprVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.A, RingVars.B', RingVars.W,
    RingVars.C, RingVars.J, RingVars.D, RingVars.E, RingVars.F,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.A, Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W,
    Jones1982.Nine.Vars.C, Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.D,
    Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F]

theorem eval_dvnd {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) :
    (fun e : Expr σ => e.eval a) v.dvnd = Jones1982.Nine.dvnd (evalExprVars a v) := by
  simp [Expr.eval, RingVars.dvnd, Jones1982.Nine.dvnd, evalExprVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.A, RingVars.B', RingVars.W,
    RingVars.C, RingVars.J, RingVars.Q, RingVars.D, RingVars.E, RingVars.F, RingVars.H,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.A, Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W,
    Jones1982.Nine.Vars.C, Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.Q,
    Jones1982.Nine.Vars.D, Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F, Jones1982.Nine.Vars.H]

theorem eval_marg {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) :
    (fun e : Expr σ => e.eval a) v.marg = Jones1982.Nine.marg (evalExprVars a v) := by
  simp [Expr.eval, RingVars.marg, Jones1982.Nine.marg, evalExprVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.P, RingVars.K,
    RingVars.B', RingVars.W, RingVars.C,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.P, Jones1982.Nine.Vars.K, Jones1982.Nine.Vars.B',
    Jones1982.Nine.Vars.W, Jones1982.Nine.Vars.C]


end DiophantineConsistency.JonesSyntax
namespace DiophantineConsistency.ExecutableJones
open NinePolynomial
theorem reused_eval_rad {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) (k : Fin 2) :
    (v.rad k).eval a = Jones1982.Nine.rad (JonesSyntax.evalExprVars a v) k :=
  JonesSyntax.eval_rad a v k

theorem reused_eval_wt {σ : Type*} (a : σ → ℤ)
    (v : RingVars (Expr σ)) (k : Fin 2) :
    (v.wt k).eval a = Jones1982.Nine.wt (JonesSyntax.evalExprVars a v) k :=
  JonesSyntax.eval_wt a v k

theorem reused_eval_dvsr {σ : Type*} (a : σ → ℤ) (v : RingVars (Expr σ)) :
    v.dvsr.eval a = Jones1982.Nine.dvsr (JonesSyntax.evalExprVars a v) :=
  JonesSyntax.eval_dvsr a v

theorem reused_eval_dvnd {σ : Type*} (a : σ → ℤ) (v : RingVars (Expr σ)) :
    v.dvnd.eval a = Jones1982.Nine.dvnd (JonesSyntax.evalExprVars a v) :=
  JonesSyntax.eval_dvnd a v

theorem reused_eval_marg {σ : Type*} (a : σ → ℤ) (v : RingVars (Expr σ)) :
    v.marg.eval a = Jones1982.Nine.marg (JonesSyntax.evalExprVars a v) :=
  JonesSyntax.eval_marg a v

end DiophantineConsistency.ExecutableJones
#print axioms DiophantineConsistency.JonesSyntax.eval_rad
#print axioms DiophantineConsistency.ExecutableJones.reused_eval_rad
#print axioms DiophantineConsistency.JonesSyntax.eval_wt
#print axioms DiophantineConsistency.ExecutableJones.reused_eval_wt
#print axioms DiophantineConsistency.JonesSyntax.eval_dvsr
#print axioms DiophantineConsistency.ExecutableJones.reused_eval_dvsr
#print axioms DiophantineConsistency.JonesSyntax.eval_dvnd
#print axioms DiophantineConsistency.ExecutableJones.reused_eval_dvnd
#print axioms DiophantineConsistency.JonesSyntax.eval_marg
#print axioms DiophantineConsistency.ExecutableJones.reused_eval_marg
