import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Cross-slice Φ-contraction for the two-parameter corridor

In the two-parameter terminal family `G_{i,j} = (A^{m+j})_{M^{n+i}}`, a negative slice
tail can only be rescued by higher-slice captures, and the balance weight
`Φ = c · M^i A^j` contracts under every such rescue.  The two finite facts are:

* `phi_transport_identity` — the exact exponent identity
  `M^{n+i'} · (M^i A^j) · A^{m+j'} = (M^{i'} A^{j'}) · M^{n+i} · A^{m+j}`,
  which converts the per-prime rescue bound `c⁻ A^{m+j} ≤ 3 c⁺ M^{n+i'}` into the
  Φ-weighted form `Φ⁻ · A^{m+j'} ≤ 3 Φ⁺ · M^{n+i}`;
* `phi_transport` — the resulting contraction step: since admissibility gives
  `M^{n+i} < A^{m+j} ≤ A^{m+j'-1}`, each rescue costs a factor `≥ A` in Φ-mass
  (`phi_contraction_factor`).

Summing the geometric source kernel (the same division-free geometric lemmas as in
`CriticalWindowContraction`) yields the paper-level conclusion recorded in the unified
report: negative slice tails carry at most an `O(1/A)` fraction of the positive Φ-mass,
so every viable two-parameter pattern is top-heavy.
-/

namespace LeanProofs.TwoBaseIntegerExponent.CrossSlice

/-- **Exponent bookkeeping.**  The transport weight identity
`M^{n+i'} (M^i A^j) A^{m+j'} = (M^{i'} A^{j'}) M^{n+i} A^{m+j}`. -/
theorem phi_transport_identity (M A : ℚ) (n m i j i' j' : ℕ) :
    M ^ (n + i') * (M ^ i * A ^ j) * A ^ (m + j')
      = (M ^ i' * A ^ j') * M ^ (n + i) * A ^ (m + j) := by
  rw [pow_add, pow_add, pow_add, pow_add]
  ring

/-- **Φ-transport step.**  If the per-prime rescue inequality
`c⁻ · A^{m+j} ≤ 3 c⁺ · M^{n+i'}` holds (count bound at a window prime of slice `j`
captured by level `(i',j')`), then in balance weights
`Φ⁻ · A^{m+j'} ≤ 3 Φ⁺ · M^{n+i}` where `Φ = c · M^i A^j`. -/
theorem phi_transport {M A cneg cpos : ℚ} {n m i j i' j' : ℕ}
    (hM : 0 < M) (hA : 0 < A)
    (hrescue : cneg * A ^ (m + j) ≤ 3 * cpos * M ^ (n + i')) :
    cneg * (M ^ i * A ^ j) * A ^ (m + j')
      ≤ 3 * (cpos * (M ^ i' * A ^ j')) * M ^ (n + i) := by
  have hAmj : (0 : ℚ) < A ^ (m + j) := pow_pos hA _
  have hkey : (cneg * (M ^ i * A ^ j) * A ^ (m + j')) * A ^ (m + j)
      ≤ (3 * (cpos * (M ^ i' * A ^ j')) * M ^ (n + i)) * A ^ (m + j) := by
    have hmul := mul_le_mul_of_nonneg_right hrescue
      (le_of_lt (by positivity : (0:ℚ) < M ^ i * A ^ j * A ^ (m + j')))
    calc (cneg * (M ^ i * A ^ j) * A ^ (m + j')) * A ^ (m + j)
        = (cneg * A ^ (m + j)) * (M ^ i * A ^ j * A ^ (m + j')) := by ring
      _ ≤ (3 * cpos * M ^ (n + i')) * (M ^ i * A ^ j * A ^ (m + j')) := hmul
      _ = 3 * cpos * (M ^ (n + i') * (M ^ i * A ^ j) * A ^ (m + j')) := by ring
      _ = 3 * cpos * ((M ^ i' * A ^ j') * M ^ (n + i) * A ^ (m + j)) := by
          rw [phi_transport_identity]
      _ = (3 * (cpos * (M ^ i' * A ^ j')) * M ^ (n + i)) * A ^ (m + j) := by ring
  exact le_of_mul_le_mul_right hkey hAmj

/-- **Contraction factor.**  Under admissibility `M^{n+i} < A^{m+j}` and a strictly
higher target slice `j < j'`, the transport weight satisfies
`M^{n+i} · A ≤ A^{m+j'}`: each cross-slice rescue costs at least one factor of `A`
in Φ-mass. -/
theorem phi_contraction_factor {M A : ℚ} {n m i j j' : ℕ}
    (hA1 : 1 ≤ A) (hM0 : 0 ≤ M)
    (hadm : M ^ (n + i) < A ^ (m + j)) (hj : j < j') :
    M ^ (n + i) * A ≤ A ^ (m + j') := by
  have h1 : M ^ (n + i) * A ≤ A ^ (m + j) * A :=
    mul_le_mul_of_nonneg_right (le_of_lt hadm) (by linarith)
  have h2 : A ^ (m + j) * A = A ^ (m + j + 1) := by rw [pow_succ]
  have h3 : A ^ (m + j + 1) ≤ A ^ (m + j') :=
    pow_le_pow_right₀ hA1 (by omega)
  calc M ^ (n + i) * A ≤ A ^ (m + j) * A := h1
    _ = A ^ (m + j + 1) := h2
    _ ≤ A ^ (m + j') := h3

end LeanProofs.TwoBaseIntegerExponent.CrossSlice
