import GowersSzemeredi.Proofs05AffineLocalization
import GowersSzemeredi.Proofs05QuadraticPhaseError
import GowersSzemeredi.Proofs05ModularPartitionTransport

/-! Refine one short proper progression after removing its small leading
quadratic term. The affine and leading-term errors each use half the budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem quadratic_chunk_phase_localization {N L : Nat} [NeZero N]
    (P : ModAP N) (phi psi : ZMod N → ZMod N) (b : ZMod N)
    (hP : P.IsProper) (hpsi : PolynomialOn 1 Finset.univ psi) (hL : 2 ≤ L)
    (hlo : quadraticLocalizationChunk L ≤ P.length)
    (hhi : P.length ≤ 2 * quadraticLocalizationChunk L)
    (hb : (centeredAbs b : Real) ≤ (N : Real) / quadraticLocalizationPrecision L)
    (hsplit : ∀ t, phi (section5ModIndexPoint P t) = b * t ^ 2 + psi t) :
    ∃ m : Nat, ∃ R : Fin m → ModAP N, ∃ z : Fin m → Complex,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      ∀ j, (R j).IsProper ∧ L ≤ (R j).length ∧ ‖z j‖ = 1 ∧
        ∀ x, x ∈ (R j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L) := by
  have hlenN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  obtain ⟨m, R, z, hpart, hcells⟩ := affine_phase_localization
    (modInterval N 0 P.length) psi (modInterval_zero_isProper hlenN) hpsi
    (by omega : 2 ≤ 2 * L) hlo
  refine ⟨m, fun j => modAPAffine P (R j), z, modAPAffine_partition P hP R hpart, fun j =>
    ⟨modAPAffine_isProper P (R j) hP (hcells j).1 (hpart.cell_subset j),
      le_trans (by omega) (hcells j).2.1, (hcells j).2.2.1, fun x hx => ?_⟩⟩
  rw [modAPAffine_carrier] at hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  have hti := hpart.cell_subset j ht
  rw [modInterval_zero_carrier] at hti
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
  rw [show P.start + P.step * (u : ZMod N) = section5ModIndexPoint P u by
    simp only [section5ModIndexPoint, mul_comm], hsplit]
  refine (norm_sub_le_norm_sub_add_norm_sub _ (exponential (-(psi u))) (z j)).trans ?_
  calc _ ≤ 1 / (8 * (L : Real)) + 1 / (4 * ((2 * L : Nat) : Real)) :=
        add_le_add (quadratic_leading_phase_error b (psi u) hL hb
          ((Finset.mem_range.mp hu).le.trans hhi)) ((hcells j).2.2.2 (u : ZMod N) ht)
    _ = 1 / (4 * L) := by push_cast; ring

end LeanProofs.GowersSzemeredi
