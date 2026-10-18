import GowersSzemeredi.Proofs05QuadraticRecurrence
import GowersSzemeredi.Proofs05QuadraticChunkLocalization
import GowersSzemeredi.Proofs05DegreeDrop
import GowersSzemeredi.Proofs05ResiduePartition

/-! Degree-two threshold-free phase localization and the complete quadratic
specialization of Corollary 5.8. No asymptotic recurrence threshold is added
to the hypotheses of the catalogue specialization. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem quadratic_phase_localization {N L : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (hP : P.IsProper)
    (hphi : PolynomialOn 2 Finset.univ phi) (hL : 2 ≤ L)
    (hsize : (2 ^ 256 * quadraticLocalizationPrecision L ^ 16) *
      (quadraticLocalizationChunk L + 1) ^ 2 ≤ P.length) :
    ∃ m : Nat, ∃ S : Fin m → ModAP N, ∃ z : Fin m → Complex,
      IsPartition (fun j => (S j).carrier) P.carrier ∧
      ∀ j, (S j).IsProper ∧ L ≤ (S j).length ∧ ‖z j‖ = 1 ∧
        ∀ x, x ∈ (S j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L) := by
  let H := quadraticLocalizationChunk L
  have hH : 1 ≤ H :=
    Nat.one_le_iff_ne_zero.mpr (by simp only [H, quadraticLocalizationChunk]; positivity)
  have hT : 2 ^ 256 * quadraticLocalizationPrecision L ^ 16 ≤ P.length :=
    (Nat.le_mul_of_pos_right _ (by positivity)).trans hsize
  have hPN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  obtain ⟨a, ha⟩ := polynomialOn_affine_degree_drop _
    (polynomialOn_section5ModIndexPoint P phi hphi)
  obtain ⟨p, hp, hpT, hrec⟩ :=
    quadratic_recurrence a (quadraticLocalization_precision_ge_two hL) (hT.trans hPN)
  obtain ⟨M, Q, _, hQpart, hQcells, hQstep⟩ := section5_residue_target_partition
    P.length p (H + 1) (by omega) (by omega)
    ((Nat.mul_le_mul_right ((H + 1) ^ 2) hpT).trans hsize)
  -- localize on each transported cell of length `H` or `H + 1`, then flatten
  have hlocal (i : Fin M) :
      ∃ m : Nat, ∃ S : Fin m → ModAP N, ∃ z : Fin m → Complex,
        IsPartition (fun j => (S j).carrier) (section5Transport P (Q i)).carrier ∧
        ∀ j, (S j).IsProper ∧ L ≤ (S j).length ∧ ‖z j‖ = 1 ∧
          ∀ x, x ∈ (S j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L) := by
    have hlength : (section5Transport P (Q i)).length = H ∨
        (section5Transport P (Q i)).length = H + 1 := by
      simpa only [section5Transport_length, Nat.add_sub_cancel] using (hQcells i).2.2
    obtain ⟨psi, hpsi, hsplit⟩ := ha ((Q i).start : ZMod N) (p : ZMod N)
    refine quadratic_chunk_phase_localization _ phi psi (a * (p : ZMod N) ^ 2)
      (section5Transport_isProper P (Q i) hP (hQcells i).1 (hQpart.cell_subset i)) hpsi hL
      (by omega) (by omega) (by simpa only [mul_comm] using hrec.le) fun t => ?_
    rw [← hsplit t]
    dsimp [section5Transport, section5ModIndexPoint, section5IndexPoint]
    rw [hQstep i]
    ring_nf
  choose m S z hpart hcells using hlocal
  let e := section5NatFlattenEquiv m
  exact ⟨∑ i, m i, fun j => S (e.symm j).1 (e.symm j).2, fun j => z (e.symm j).1 (e.symm j).2,
    finsetPartition_flatten m _ P.carrier (fun i j => (S i j).carrier)
      (section5Transport_partition P Q hP hQpart) hpart,
    fun j => hcells (e.symm j).1 (e.symm j).2⟩

theorem thresholdFreePolynomialLocalization_two : ThresholdFreePolynomialLocalization 2 := by
  intro N _ P phi L hP hphi hL hsize
  exact quadratic_phase_localization P phi hP hphi hL
    ((quadraticLocalization_chunk_budget hL).trans hsize)

end LeanProofs.GowersSzemeredi
