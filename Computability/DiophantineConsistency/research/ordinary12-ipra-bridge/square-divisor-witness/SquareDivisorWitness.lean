import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace SquareDivisorWitness

/-- A Bézout certificate for `a,b` supplies one for their squares. -/
theorem square_bezout {R : Type*} [CommRing R] (a b x y : R)
    (h : a*x+b*y=1) :
    a^2*(a*x^3+3*b*x^2*y)+b^2*(3*a*x*y^2+b*y^3)=1 := by
  calc
    a^2*(a*x^3+3*b*x^2*y)+b^2*(3*a*x*y^2+b*y^3) = (a*x+b*y)^3 := by ring
    _ = 1 := by rw [h]; ring

/-- Explicitly recover a square-divisor witness from the cleared norm and
Bézout certificate. This polynomial identity needs no cancellation,
positivity, integral-domain hypothesis, or choice of a quotient. -/
theorem norm_square_divisor {R : Type*} [CommRing R] (q v a b x y : R)
    (h : a*x+b*y=1)
    (hnorm : q*v^2*b^2=(q-1)*a^2+b^2) :
    q-1 = b^2*((q*v^2-1)*(a*x^3+3*b*x^2*y) +
      (q-1)*(3*a*x*y^2+b*y^3)) := by
  have hfactor : (q-1)*a^2 = b^2*(q*v^2-1) := by
    calc
      (q-1)*a^2 = (q-1)*a^2+b^2-b^2 := by ring
      _ = q*v^2*b^2-b^2 := by rw [hnorm]
      _ = b^2*(q*v^2-1) := by ring
  calc
    q-1 = (q-1)*(a^2*(a*x^3+3*b*x^2*y)+b^2*(3*a*x*y^2+b*y^3)) := by
      rw [square_bezout a b x y h]; ring
    _ = ((q-1)*a^2)*(a*x^3+3*b*x^2*y)+b^2*((q-1)*(3*a*x*y^2+b*y^3)) := by ring
    _ = b^2*((q*v^2-1)*(a*x^3+3*b*x^2*y)+(q-1)*(3*a*x*y^2+b*y^3)) := by rw [hfactor]; ring

end SquareDivisorWitness

#print axioms SquareDivisorWitness.square_bezout
#print axioms SquareDivisorWitness.norm_square_divisor
