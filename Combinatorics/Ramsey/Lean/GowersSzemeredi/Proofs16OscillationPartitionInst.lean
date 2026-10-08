import GowersSzemeredi.Proofs16OscillationPartition
import GowersSzemeredi.Proofs05SimultaneousMultiaffinePartition

/-! Discharging `MultilinearDiameterPartition` with the peer's theorem.

`MultilinearDiameterPartition K p` is, word for word, the dimension-two body
of `exists_simultaneous_multilinear_partition_bound`. This module imports the
OAI port through `Proofs05SchmidtRecurrence`, so it is checked only on the
full-verification host. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The multilinear partition theorem in dimension two, with a polynomial
exponent `p (q + 1)^8` in the number `q` of maps. -/
theorem exists_multilinearDiameterPartition :
    ∃ (K : Real) (p : Nat), 2 ≤ K ∧ 0 < p ∧ MultilinearDiameterPartition K p := by
  obtain ⟨K, p, hK, hp, h⟩ := exists_simultaneous_multilinear_partition_bound 2 (by norm_num)
  exact ⟨K, p, hK, hp, h⟩

end LeanProofs.GowersSzemeredi
