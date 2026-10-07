import Mathlib.Data.ZMod.Basic
import OAI.Combinatorics.Progressions.FixedDensity.Energy

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure AffineForm (ι R : Type*) [Zero R] where
  constant : R
  coefficient : ι → R

namespace AffineForm

def eval {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) (x : ι → R) : R :=
  ψ.constant + ∑ i, ψ.coefficient i * x i

@[simp]
theorem eval_zero {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) :
    ψ.eval (fun _ => 0) = ψ.constant := by
  simp [eval]

end AffineForm

abbrev CubePoint (k N : ℕ) :=
  Fin k → Bool → ZMod N

abbrev DeletedCube (k : ℕ) (j : Fin k) :=
  {i : Fin k // i ≠ j} → Bool

def apLinearForm (k N : ℕ) (j : Fin k) (ω : DeletedCube k j)
    (x : CubePoint k N) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i.1 (ω i)

abbrev LinearFormsExponent (k : ℕ) :=
  (j : Fin k) → DeletedCube k j → Bool

def linearFormsProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (e : LinearFormsExponent k) (x : CubePoint k N) : ℝ :=
  ∏ j : Fin k, ∏ ω : DeletedCube k j,
    if e j ω then ν (apLinearForm k N j ω x) else 1

def HasLinearFormsCondition (k N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (η : ℝ) : Prop :=
  ∀ e : LinearFormsExponent k,
    |mean (linearFormsProduct k N ν e) - 1| ≤ η

theorem HasLinearFormsCondition.mono {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η η' : ℝ}
    (hν : HasLinearFormsCondition k N ν η) (hη : η ≤ η') :
    HasLinearFormsCondition k N ν η' :=
  fun e => (hν e).trans hη

end Erdos3.FixedDensity

end

end OAI
