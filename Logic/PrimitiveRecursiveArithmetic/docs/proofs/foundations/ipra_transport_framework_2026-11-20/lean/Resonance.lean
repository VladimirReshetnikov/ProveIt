import Std

/-! Finite algebra used by the resonant Gauss construction. A field argument
is a host parameter. The formalization plan in the report specializes the
identities to coded Gaussian rationals inside first-order iPRA. -/

namespace Resonance
section
variable {K : Type} [Lean.Grind.Field K]

/-- Coefficient of a primitive at an ordinary exponent and at the exceptional
logarithm. The first coordinate multiplies a monomial, the second its log. -/
def primitiveEntry [DecidableEq K] (exponent coefficient : K) : K × K :=
  if exponent = 0 then (0, coefficient) else (coefficient / exponent, 0)

theorem recoverEntry [DecidableEq K] (e c : K) :
    (primitiveEntry e c).1 * e + (primitiveEntry e c).2 = c := by
  by_cases h : e = 0
  · simp [primitiveEntry, h] <;> grind
  · simp [primitiveEntry, h] <;> grind

/-- Pointwise algebra for reduction of order, with v the derivative of u,
and b the derivative of h. -/
theorem productWronskian (u v h b : K) :
    u * (v*h + u*b) - v*(u*h) = u*u*b := by grind

/-- The ODE for a second column follows from its Wronskian law. -/
theorem secondColumn (u du ddu v dv ddv p q : K)
    (unit : u ≠ 0)
    (first : ddu + p * du + q * u = 0)
    (wronskian : u*ddv - ddu*v = -p * (u*dv - du*v)) :
    ddv + p*dv + q*v = 0 := by
  have h : u*(ddv + p*dv + q*v) = 0 := by grind
  grind

def prefixProduct (factor : Nat → K) : Nat → K
  | 0 => 1
  | n+1 => prefixProduct factor n * factor n

/-- Telescope a rational coefficient recurrence without ever cancelling a
numerator. This covers terminating upper parameters. -/
theorem prefixRecovery (top bot values : Nat → K) (n : Nat)
    (step : ∀ j, j < n → bot j * values (j+1) = top j * values j) :
    prefixProduct bot n * values n = prefixProduct top n * values 0 := by
  induction n with
  | zero => simp [prefixProduct]
  | succ n ih =>
    have prev := ih (fun j hj => step j (by omega))
    have here := step n (by omega)
    simp only [prefixProduct]
    calc
      _ = prefixProduct bot n * (bot n * values (n+1)) := by grind
      _ = prefixProduct bot n * (top n * values n) := by rw [here]
      _ = (prefixProduct bot n * values n) * top n := by grind
      _ = _ := by rw [prev]; grind

/-- At the singular recurrence index the new unknown is the log coefficient.
Take n = k-1, last = k, values(0) = -1/k. -/
theorem logObstruction (top bot values : Nat → K) (n : Nat) (last coeff : K)
    (step : ∀ j, j < n → bot j * values (j+1) = top j * values j)
    (exceptional : last * coeff = top n * values n) :
    prefixProduct bot n * (last * coeff) =
    prefixProduct top (n+1) * values 0 := by
  have prev := prefixRecovery top bot values n step
  rw [exceptional]
  simp only [prefixProduct]
  calc
    _ = (prefixProduct bot n * values n) * top n := by grind
    _ = _ := by rw [prev]; grind

/-- Matching initial jets by Wronskian cofactors; every later precision
argument can use these cross-multiplied identities. -/
theorem matchingCofactors (u du v dv y dy : K) :
    ((y*dv-dy*v)*u + (u*dy-du*y)*v = (u*dv-du*v)*y) ∧
    ((y*dv-dy*v)*du + (u*dy-du*y)*dv = (u*dv-du*v)*dy) := by
  constructor <;> grind

end
end Resonance
