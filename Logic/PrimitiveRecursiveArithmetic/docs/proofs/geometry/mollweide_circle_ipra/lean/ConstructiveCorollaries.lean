import MollweideCircleIPRA.AlgebraicCore

/-!
# Constructive quotient and cancellation corollaries

These lemmas exhibit the exact apartness assumptions needed to pass from the
polynomial core to familiar quotient statements.  They are ambient ordered-
field lemmas, not yet object-language iPRA derivations.

Formalization status: proposed script, not compiled in the delivery environment.
-/

namespace MollweideCircleIPRA

section OrderedField

variable {R : Type*} [LinearOrderedField R]

/-- Familiar first Mollweide quotient from its denominator-free form. -/
theorem mollweide_sum_quotient
    (a b c sC cD : R)
    (hc : c ≠ 0) (hsC : sC ≠ 0)
    (h : (a + b) * sC = c * cD) :
    (a + b) / c = cD / sC := by
  apply (div_eq_div_iff hc hsC).2
  simpa [mul_comm] using h

/-- Familiar second Mollweide quotient from its denominator-free form. -/
theorem mollweide_difference_quotient
    (a b c cC sD : R)
    (hc : c ≠ 0) (hcC : cC ≠ 0)
    (h : (a - b) * cC = c * sD) :
    (a - b) / c = sD / cC := by
  apply (div_eq_div_iff hc hcC).2
  simpa [mul_comm] using h

/-- Quotient form of the law of tangents.  The right side is
`tan((A-B)/2) / tan((A+B)/2)` after `tan((A+B)/2)=cC/sC`. -/
theorem lawOfTangents_quotient
    (a b sD cD sC cC : R)
    (hab : a + b ≠ 0) (hcD : cD ≠ 0) (hcC : cC ≠ 0)
    (hCross : (a - b) * cD * cC = (a + b) * sD * sC) :
    (a - b) / (a + b) = (sD * sC) / (cD * cC) := by
  apply (div_eq_div_iff hab (mul_ne_zero hcD hcC)).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using hCross

/-- One branch of the law of cotangents.  The equation `r*cA=x*sA`
is exactly the denominator-free statement. -/
theorem cotangent_over_excess
    (r x sA cA : R)
    (hr : r ≠ 0) (hx : x ≠ 0) (hsA : sA ≠ 0)
    (h : r * cA = x * sA) :
    (cA / sA) / x = 1 / r := by
  field_simp [hr, hx, hsA]
  simpa [mul_comm] using h

/-- Heron plus `r*s=K` gives the inradius square formula by one
constructively licensed cancellation of the apart factor `s`. -/
theorem inradius_squared_cross
    (K r s x y z : R)
    (hs : s ≠ 0)
    (hHeron : K ^ 2 = s * x * y * z)
    (hRadius : r * s = K) :
    r ^ 2 * s = x * y * z := by
  have hsq : (r * s) ^ 2 = K ^ 2 := by rw [hRadius]
  have hmul : (r ^ 2 * s - x * y * z) * s = 0 := by
    calc
      (r ^ 2 * s - x * y * z) * s = (r * s) ^ 2 - s * x * y * z := by ring
      _ = K ^ 2 - s * x * y * z := by rw [hsq]
      _ = 0 := by rw [hHeron]; ring
  have hz : r ^ 2 * s - x * y * z = 0 :=
    (mul_eq_zero.mp hmul).resolve_right hs
  exact sub_eq_zero.mp hz

/-- A line meeting a circle at two apart parameters has signed parameter
product equal to the power divided by the direction norm square. -/
theorem signed_secant_product
    (p h q u w : R)
    (hfu : p + 2 * h * u + q * u ^ 2 = 0)
    (hfw : p + 2 * h * w + q * w ^ 2 = 0)
    (hwu : w ≠ u) :
    p = q * u * w := by
  have hfac : (w - u) * (p - q * u * w) = 0 := by
    rw [← secant_factor_identity p h q u w, hfu, hfw]
    ring
  have hne : w - u ≠ 0 := sub_ne_zero.mpr hwu
  have hz : p - q * u * w = 0 := (mul_eq_zero.mp hfac).resolve_left hne
  exact sub_eq_zero.mp hz

/-- Tangent power once the tangent point lies on the circle and the direction
is orthogonal to the radius. -/
theorem tangent_power
    (tx ty ox oy vx vy t rho : R)
    (hon : normSq (tx - ox) (ty - oy) - rho = 0)
    (hperp : dot (tx - ox) (ty - oy) vx vy = 0) :
    normSq (tx - t * vx - ox) (ty - t * vy - oy) - rho =
      normSq vx vy * t ^ 2 := by
  rw [tangent_power_decomposition, hon, hperp]
  ring

end OrderedField

end MollweideCircleIPRA
