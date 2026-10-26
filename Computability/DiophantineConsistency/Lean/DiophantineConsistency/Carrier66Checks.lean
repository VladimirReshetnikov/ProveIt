import DiophantineConsistency.Carrier66

/-!
# Focused checks of the fifteen-coordinate parent and both coordinate maps

The symbolic checks bind the independent h and tau slots to the displayed
P66 interface.  In particular the fixed placeholder in `core` cannot
replace the independent first root or introduce another unknown.
-/

namespace DiophantineConsistency.Carrier66Checks

open Carrier66

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) : (core p v).tau = v 10 := rfl

example (beta K MC MF J F alpha z f h i T s w tau eta zeta y gamma : ℤ) :
    index ![beta, K, MC, MF]
      ![J, F, alpha, z, f, h, i, T, s, w, tau, eta, zeta, y, gamma] =
      eta + zeta - h * ((w * (beta * J + 1)) * (s * (beta * J + 1) ^ 3)) -
        ((beta * J * (beta * J + 1 - F) + alpha) * ((beta * J + 1) ^ 2 - 1) +
          (MC + (beta * J + 1) * MF) * J) := by
  rfl

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    (core p v).P = (v 10) ^ 2 - (core p v).ell * ((core p v).ell + (core p v).k) := rfl

example (p : Fin 4 → ℤ) (v : Fin 14 → ℤ) (h : ℤ) :
    drop (restore p v h) (v 9) = v := drop_restore p v h

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (n : ℤ)
    (ht : v 10 = (core p v).E * n + (core p v).k - (core p v).rank) :
    restore p (drop v n) (v 5) = v := restore_drop p v n ht

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) (hc : Canonical p v) :
    MvPolynomial.eval v (polynomial p) = 0 := by
  rw [eval_polynomial]
  exact canonical_zero p v hc

#print axioms core_restore
#print axioms placeholder_irrelevant
#print axioms core_drop_of_carrier
#print axioms value_restore
#print axioms value_map
#print axioms eval_polynomial
#print axioms positive_zero_restores_canonical
#print axioms canonical_drops_to_positive_zero
#print axioms exists_positive_polynomial_zero_iff_canonical
#print axioms exists_positive_polynomial_zero_iff_canonical_parent_zero

end DiophantineConsistency.Carrier66Checks
