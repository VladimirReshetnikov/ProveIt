import DiophantineConsistency.ThirteenCarrier

open DiophantineConsistency.ThirteenCarrier

-- The deleted-transport scale includes b exactly once, at the actual i slot.
example (beta K MC MF J F alpha f i T s w n eta zeta m gamma : ℤ) :
    (core ![beta, K, MC, MF] ![J, F, alpha, f, i, T, s, w, n, eta, zeta, m, gamma]).t =
      (beta * J) * i * ((eta + zeta) * (s * (beta * J + 1) ^ 3) + eta) ^ 2 := rfl

-- Positive independent coordinates do not imply positivity of the signed abbreviation.
example : (core ![31, 2, 3, 4] (fun _ => (1 : ℤ))).y < 0 := by decide

example : (core ![31, 2, 3, 4] (fun _ => (1 : ℤ))).y =
    1 + 4 * (31 * (1 - (-984257) ^ 2 * 89) - 89) := by decide

#print axioms scaled_identity
#print axioms value69_zero_iff_value71_zero
#print axioms positive_polynomial_zero_sets
