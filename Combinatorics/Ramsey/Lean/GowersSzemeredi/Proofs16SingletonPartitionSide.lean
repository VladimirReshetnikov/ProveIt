import GowersSzemeredi.Proofs16SingletonPartition

/-! Declarations of `Proofs16SingletonPartition` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Width targets at most one need no frequency or Bohr hypotheses. -/
theorem section16_local_linearity_singletons {N k : Nat} [NeZero N]
    (P : Box N (k + 1)) (l : Real) (hl : l ≤ 1)
    (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N) :
    ∃ M : Nat, ∃ Q : Fin M → Box N (k + 1),
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, l ≤ (Q j).width) ∧
      ∀ j x, LinearOn (((Q j).axis (Fin.last k)).carrier.filter fun y => y ∈ A x) (f x) := by
  obtain ⟨M, x, hpart⟩ := box_singleton_partition P
  refine ⟨M, fun j => pointSingletonBox (x j), hpart,
    fun j => pointSingletonBox_isProper _, ?_, ?_⟩
  · intro j
    simpa only [pointSingletonBox_width (by omega : 0 < k + 1), Nat.cast_one] using hl
  · intro j z
    apply LinearOn.of_subset_singleton _ _ ((x j) (Fin.last k))
    intro y hy
    simpa only [pointSingletonBox_axis_carrier] using (Finset.mem_filter.mp hy).1

end LeanProofs.GowersSzemeredi
