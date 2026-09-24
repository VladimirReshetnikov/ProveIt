import Diophantine.Paper1982.Ratio
import Diophantine.Paper1982.Psi
import Diophantine.Paper1982.PellQuotient

/-!
# The polynomial ratio subsystem in Jones 1982, Theorem 3

These are the ten equations obtained from Lemma 2.25 and Corollary 2.29
after eliminating the auxiliary variables. All witnesses range over the
natural numbers; every displayed subtraction is interpreted over `ℤ`.
Strict positivity is supplied separately by the equivalence theorems.
-/

namespace Jones1982

/-- The last ten equations of Theorem 3, with `R = r` and `N = n`.
Here `w` is the positive multiplier of Lemma 2.25, not an exponent for `b`. -/
structure RatioPolynomial (R N b a c d f h i j k o p s w γ η τ φ : ℕ) : Prop where
  Pdef : p = 2 * w * s ^ 2 * R ^ 2 * N ^ 6
  pellP : (p : ℤ) ^ 2 * k ^ 2 - k ^ 2 + 1 = (τ : ℤ) ^ 2
  close : 4 * ((c : ℤ) - k * s * N ^ 2) ^ 2 + η = (k : ℤ) ^ 2
  Kdef : (k : ℤ) = R + 1 + h * p - h
  Adef : a = (w * N ^ 2 + 1) * R * s * N ^ 2
  Cdef : c = 2 * R + 1 + φ
  Ddef : (d : ℤ) = b * w + c * a - 2 * c + 4 * a * γ - 5 * γ
  pellD : (d : ℤ) ^ 2 = ((a : ℤ) ^ 2 - 1) * c ^ 2 + 1
  pellF : (f : ℤ) ^ 2 = ((a : ℤ) ^ 2 - 1) * i ^ 2 * c ^ 4 + 1
  pellDF : ((d : ℤ) + o * f) ^ 2 =
    (((a : ℤ) + f ^ 2 * (d ^ 2 - a)) ^ 2 - 1) * (2 * R + 1 + j * c) ^ 2 + 1

end Jones1982
