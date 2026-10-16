import GowersSzemeredi.Proofs16ProductRecurrence

/-! # Short proper cells retaining the lifted product recurrence -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- A finite multilinear cover of the frequencies gives a common-difference
Bohr element on every selected base point. -/
theorem product_recurrence_bohr_mem {N k q : Nat} [NeZero N]
    (mu : Fin q → Point N k → ZMod N) (K : Point N k → Finset (ZMod N))
    (x : Point N k) (d : ZMod N) (e zeta : Real) (v : Nat)
    (hcover : ∀ r ∈ K x, ∃ i, r = mu i x)
    (hsmall : ∀ i, (centeredAbs (mu i x * d) : Real) ≤ e * N)
    (hbudget : e ≤ zeta / v) : d ∈ bohr (K x) (zeta / v) := by
  classical
  simp only [bohr, Finset.mem_filter, Finset.mem_univ, true_and]
  intro r hr
  obtain ⟨i, rfl⟩ := hcover r hr
  exact (hsmall i).trans (mul_le_mul_of_nonneg_right hbudget (Nat.cast_nonneg N))

end LeanProofs.GowersSzemeredi
