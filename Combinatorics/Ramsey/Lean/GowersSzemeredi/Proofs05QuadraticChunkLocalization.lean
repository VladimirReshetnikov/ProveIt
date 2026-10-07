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
  classical
  have hlenN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  obtain ⟨m, R, z, hpart, hcells⟩ := affine_phase_localization
    (modInterval N 0 P.length) psi (modInterval_zero_isProper hlenN) hpsi
    (by omega : 2 ≤ 2 * L) hlo
  refine ⟨m, fun j => modAPAffine P (R j), z, modAPAffine_partition P hP R hpart, ?_⟩
  intro j
  refine ⟨modAPAffine_isProper P (R j) hP (hcells j).1 (hpart.cell_subset j),
    ?_, (hcells j).2.2.1, ?_⟩
  · change L ≤ (R j).length
    have := (hcells j).2.1
    omega
  · intro x hx
    rw [modAPAffine_carrier] at hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    have hti := hpart.cell_subset j ht
    rw [modInterval_zero_carrier] at hti
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hti
    have hu' : u ≤ 2 * quadraticLocalizationChunk L :=
      (Finset.mem_range.mp hu).le.trans hhi
    have heq : P.start + P.step * (u : ZMod N) = section5ModIndexPoint P (u : ZMod N) := by
      simp only [section5ModIndexPoint, mul_comm]
    rw [heq, hsplit]
    have herror := quadratic_leading_phase_error b (psi (u : ZMod N)) hL hb hu'
    have haff := (hcells j).2.2.2 (u : ZMod N) ht
    have hsum := norm_sub_le_norm_sub_add_norm_sub (exponential (-(b * (u : ZMod N) ^ 2 + psi (u : ZMod N))))
      (exponential (-(psi (u : ZMod N)))) (z j)
    have hden : (4 : Real) * ((2 * L : Nat) : Real) = 8 * L := by push_cast; ring
    rw [hden] at haff
    have he : (1 : Real) / (8 * L) + 1 / (8 * L) = 1 / (4 * L) := by ring
    linarith

end LeanProofs.GowersSzemeredi
