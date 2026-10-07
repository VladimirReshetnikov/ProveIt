import GowersSzemeredi.Proofs05AffineLocalization
import GowersSzemeredi.Proofs05FiniteLocalizationPhaseError
import GowersSzemeredi.Proofs05ModularPartitionTransport

/-! Refine a short proper progression using localization in the previous
degree and a small leading monomial. Each error uses half the budget. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem polynomial_chunk_phase_localization {N k L : Nat} [NeZero N]
    (hloc : ThresholdFreePolynomialLocalization k)
    (P : ModAP N) (phi psi : ZMod N → ZMod N) (b : ZMod N)
    (hP : P.IsProper) (hpsi : PolynomialOn k Finset.univ psi) (hL : 2 ≤ L)
    (hlo : finiteLocalizationChunk k L ≤ P.length)
    (hhi : P.length ≤ 2 * finiteLocalizationChunk k L)
    (hb : (centeredAbs b : Real) ≤ (N : Real) / finiteLocalizationPrecision (k + 1) L (finiteLocalizationChunk k L))
    (hsplit : ∀ t, phi (section5ModIndexPoint P t) = b * t ^ (k + 1) + psi t) :
    ∃ m : Nat, ∃ R : Fin m → ModAP N, ∃ z : Fin m → Complex,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      ∀ j, (R j).IsProper ∧ L ≤ (R j).length ∧ ‖z j‖ = 1 ∧
        ∀ x, x ∈ (R j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L) := by
  classical
  have hlenN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  obtain ⟨m, R, z, hpart, hcells⟩ := hloc N
    (modInterval N 0 P.length) psi (2 * L) (modInterval_zero_isProper hlenN) hpsi
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
    have hu' : u ≤ 2 * finiteLocalizationChunk k L :=
      (Finset.mem_range.mp hu).le.trans hhi
    have heq : P.start + P.step * (u : ZMod N) = section5ModIndexPoint P (u : ZMod N) := by
      simp only [section5ModIndexPoint, mul_comm]
    rw [heq, hsplit]
    have herror := polynomial_leading_phase_error b (psi (u : ZMod N)) hL
      (finiteLocalizationChunk_bounds (k := k) hL).1 hb hu'
    have haff := (hcells j).2.2.2 (u : ZMod N) ht
    have hsum := norm_sub_le_norm_sub_add_norm_sub (exponential (-(b * (u : ZMod N) ^ (k + 1) + psi (u : ZMod N))))
      (exponential (-(psi (u : ZMod N)))) (z j)
    have hden : (4 : Real) * ((2 * L : Nat) : Real) = 8 * L := by push_cast; ring
    rw [hden] at haff
    have he : (1 : Real) / (8 * L) + 1 / (8 * L) = 1 / (4 * L) := by ring
    linarith

end LeanProofs.GowersSzemeredi
