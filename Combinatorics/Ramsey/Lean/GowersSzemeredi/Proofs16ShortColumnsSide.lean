import GowersSzemeredi.Proofs16ShortColumns
import GowersSzemeredi.Proofs16AnchoredCoverSide

/-! Declarations of `Proofs16ShortColumns` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- Directly sampled columns use constant-in-the-last-variable lifts.
All other certified points use the paired interpolants. -/
theorem Section16SampledOrAnchoredOn.multilinear_cover {N k r p : Nat} [NeZero N]
    {D F : Finset (Point N (k + 1))} {phi : Point N (k + 1) → ZMod N}
    {sample : Fin r → ZMod N} (ha : Section16SampledOrAnchoredOn D phi sample F)
    (H : Finset (Point N k)) (mu : Fin r → Fin p → Point N k → ZMod N)
    (hmu : ∀ i j, IsMultilinear (mu i j))
    (hcover : ∀ h ∈ H, ∀ i, appendCoordinate h (sample i) ∈ D →
      appendCoordinate h (sample i) ∈ F →
      ∃ j, phi (appendCoordinate h (sample i)) = mu i j h) :
    ∃ M : ((Fin r × Fin p) ⊕ (Fin r × Fin r × Fin p × Fin p)) → Point N (k + 1) → ZMod N,
      (∀ ij, IsMultilinear (M ij)) ∧
      ∀ h ∈ H, ∀ x, appendCoordinate h x ∈ D → appendCoordinate h x ∈ F →
        ∃ ij, phi (appendCoordinate h x) = M ij (appendCoordinate h x) := by
  obtain ⟨K, hK, hanchor, hrecovered⟩ := ha
  obtain ⟨nu, hnu, hnc⟩ := hanchor.multilinear_cover H mu hmu
    (fun h hh i hi hk => hcover h hh i hi (hK hk))
  refine ⟨Sum.elim (fun ij z => mu ij.1 ij.2 (Fin.init z)) nu, ?_, ?_⟩
  · intro ij
    cases ij with
    | inl ij => exact (hmu ij.1 ij.2).lift_last
    | inr ij => exact hnu ij
  · intro h hh x hxD hxF
    rcases hrecovered h x hxD hxF with hxK | ⟨i, rfl⟩
    · obtain ⟨ij, heq⟩ := hnc h hh x hxD hxK
      exact ⟨Sum.inr ij, heq⟩
    · obtain ⟨j, hj⟩ := hcover h hh i hxD hxF
      refine ⟨Sum.inl (i, j), ?_⟩
      simpa [appendCoordinate_eq_snoc] using hj

end LeanProofs.GowersSzemeredi
