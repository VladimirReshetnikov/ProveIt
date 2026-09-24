/-
Illustrative code accompanying Foundations for Surreal and Surcomplex Mathematics.
Status: NOT COMPILED in the environment used to prepare the article.
Requires Mathlib. This is a componentwise arithmetic sketch, NOT a full ring,
field, norm, real-closedness, or surreal construction.
-/
import Mathlib.Algebra.Ring.Basic

universe u

namespace SurcomplexFoundations

/-- A separate carrier avoids accidentally using the product-ring multiplication. -/
structure Complexify (R : Type u) where
  re : R
  im : R

namespace Complexify

variable {R : Type u} [CommRing R]

def one : Complexify R := { re := 1, im := 0 }
def imaginaryUnit : Complexify R := { re := 0, im := 1 }
def neg (z : Complexify R) : Complexify R :=
  { re := -z.re, im := -z.im }
def mul (z w : Complexify R) : Complexify R :=
  { re := z.re * w.re - z.im * w.im,
    im := z.re * w.im + z.im * w.re }

theorem imaginaryUnit_sq :
    mul (imaginaryUnit : Complexify R) imaginaryUnit = neg one := by
  simp [mul, imaginaryUnit, neg, one]

end Complexify
end SurcomplexFoundations
