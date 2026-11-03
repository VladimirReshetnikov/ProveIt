import DiophantineConsistency.Representation
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Degree bounds for supplied arithmetic syntax with weighted inputs -/

namespace DiophantineConsistency.Expr

variable {σ : Type*}

def evalRing {R : Type*} [CommRing R] (v : σ → R) : Expr σ → R
  | .constant z => (z : R)
  | .var i => v i
  | .add p q => p.evalRing v+q.evalRing v
  | .sub p q => p.evalRing v-q.evalRing v
  | .mul p q => p.evalRing v*q.evalRing v

@[simp] theorem evalRing_constant {R : Type*} [CommRing R] (v : σ → R) (z : ℤ) :
    (constant z).evalRing v=(z : R) := rfl

@[simp] theorem evalRing_var {R : Type*} [CommRing R] (v : σ → R) (i : σ) :
    (var i).evalRing v=v i := rfl

@[simp] theorem evalRing_add {R : Type*} [CommRing R] (v : σ → R) (p q : Expr σ) :
    (p+q).evalRing v=p.evalRing v+q.evalRing v := rfl

@[simp] theorem evalRing_sub {R : Type*} [CommRing R] (v : σ → R) (p q : Expr σ) :
    (p-q).evalRing v=p.evalRing v-q.evalRing v := rfl

@[simp] theorem evalRing_mul {R : Type*} [CommRing R] (v : σ → R) (p q : Expr σ) :
    (p*q).evalRing v=p.evalRing v*q.evalRing v := rfl

@[simp] theorem evalRing_ofNat {R : Type*} [CommRing R] (v : σ → R) (n : ℕ) :
    (ofNat(n) : Expr σ).evalRing v=(n : R) := by
  change ((n : ℤ) : R)=(n : R)
  exact Int.cast_natCast n

def weightedDegree (w : σ → ℕ) : Expr σ → ℕ
  | .constant _ => 0
  | .var i => w i
  | .add p q | .sub p q => max (p.weightedDegree w) (q.weightedDegree w)
  | .mul p q => p.weightedDegree w+q.weightedDegree w

@[simp] theorem evalRing_pow {R : Type*} [CommRing R] (e : Expr σ) (n : ℕ) (v : σ → R) :
    (e^n).evalRing v=(e.evalRing v)^n := by
  change (e.pow n).evalRing v=_
  induction n <;> simp_all [pow,evalRing,pow_succ]

theorem degree_evalRing_le {τ : Type*} (e : Expr σ) (w : σ → ℕ)
    (v : σ → MvPolynomial τ ℤ) (hv : ∀ i,(v i).totalDegree ≤ w i) :
    (e.evalRing v).totalDegree ≤ e.weightedDegree w := by
  induction e with
  | constant z =>
    change (MvPolynomial.C z : MvPolynomial τ ℤ).totalDegree ≤ 0
    rw [MvPolynomial.totalDegree_C]
  | var i => exact hv i
  | add p q hp hq => exact (MvPolynomial.totalDegree_add _ _).trans (max_le_max hp hq)
  | sub p q hp hq => exact (MvPolynomial.totalDegree_sub _ _).trans (max_le_max hp hq)
  | mul p q hp hq => exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add hp hq)

/-- The generic interpretation is the usual polynomial at its own variables. -/
theorem evalRing_X (e : Expr σ) : e.evalRing (MvPolynomial.X : σ → MvPolynomial σ ℤ)=e.toPolynomial := by
  induction e <;> simp_all [evalRing,toPolynomial]

end DiophantineConsistency.Expr
