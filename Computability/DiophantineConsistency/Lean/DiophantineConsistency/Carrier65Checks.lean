import DiophantineConsistency.Carrier65

/-!
# Focused checks for the literal Carrier65 front

The first check fixes all fourteen coordinate slots and the four port slots
against the displayed carrier.  The numerical checks exercise the source-mask
port without an additional beta shift.  The last check deliberately makes
tau negative: the first-norm obstruction still applies, and no sign premise
on that abbreviation is smuggled into the zero-sign theorem.
-/

namespace DiophantineConsistency.Carrier65Checks

open Carrier65

example (beta K MC MF J F alpha z f i T s w n eta zeta y gamma : ℤ) :
    (core ![beta, K, MC, MF] ![J, F, alpha, z, f, i, T, s, w, n, eta, zeta, y, gamma]).tau =
      (w * (beta * J + 1)) * (s * (beta * J + 1) ^ 3) * n + (eta + zeta) -
        ((beta * J * (beta * J + 1 - F) + alpha) * ((beta * J + 1) ^ 2 - 1) +
          (MC + (beta * J + 1) * MF) * J) := by
  rfl

example :
    (core ![31, 2, 3, 4] (fun _ => (1 : ℤ))).q = 32 ∧
    (core ![31, 2, 3, 4] (fun _ => (1 : ℤ))).rank = 984257 ∧
    (core ![31, 2, 3, 4] (fun _ => (1 : ℤ))).tau = 64321 ∧
    (core ![31, 2, 3, 4] (fun _ => (1 : ℤ))).W = 90 := by
  decide

example : value ![31, 2, 3, 4] (fun _ => (1 : ℤ)) ≠ 0 := by
  intro hzero
  have hW := ((value_zero_iff_norms ![31, 2, 3, 4] (fun _ => (1 : ℤ))
    (by norm_num) (by intro j; norm_num)).mp hzero).2.2.2.2
  norm_num [core, Matrix.cons_val] at hW

example :
    (core ![31, 2, 3, 1000000] (fun _ => (1 : ℤ))).tau = -31935551 ∧
    (core ![31, 2, 3, 1000000] (fun _ => (1 : ℤ))).P ≠ -1 := by
  constructor
  · decide
  · rw [first_shape]
    exact ConsecutivePell.norm_ne_neg_one _ _ _
      (firstParameter_ge_two _ _ (by norm_num) (by intro j; norm_num))

#print axioms value_map
#print axioms eval_polynomial
#print axioms value_zero_iff_norms
#print axioms scaled_strong_eq_delta
#print axioms eval_polynomial_zero_iff_norms

end DiophantineConsistency.Carrier65Checks
