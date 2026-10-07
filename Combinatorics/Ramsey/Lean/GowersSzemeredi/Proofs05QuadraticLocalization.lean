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
  classical
  let H := quadraticLocalizationChunk L
  let R := quadraticLocalizationPrecision L
  let T := 2 ^ 256 * R ^ 16
  have hH : 1 ≤ H := by
    dsimp [H, quadraticLocalizationChunk]
    have : 1 ≤ (2 * L) ^ 3 := one_le_pow₀ (by omega)
    omega
  have hR : 2 ≤ R := quadraticLocalization_precision_ge_two hL
  have hbudget : T * (H + 1) ^ 2 ≤ P.length := hsize
  have hT : T ≤ P.length := by
    calc
      T = T * 1 := (Nat.mul_one T).symm
      _ ≤ T * (H + 1) ^ 2 := Nat.mul_le_mul_left T (one_le_pow₀ (by omega))
      _ ≤ _ := hbudget
  have hPN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  let f : ZMod N → ZMod N := fun x => phi (section5ModIndexPoint P x)
  have hf : PolynomialOn 2 Finset.univ f := polynomialOn_section5ModIndexPoint P phi hphi
  obtain ⟨a, ha⟩ := polynomialOn_affine_degree_drop f hf
  obtain ⟨p, hp, hpT, hrec⟩ := quadratic_recurrence a hR (hT.trans hPN)
  obtain ⟨M, Q, hM, hQpart, hQcells, hQstep⟩ := section5_residue_target_partition
    P.length p (H + 1) (by omega) (by omega)
    ((Nat.mul_le_mul_right ((H + 1) ^ 2) hpT).trans hbudget)
  let C : Fin M → ModAP N := fun i => section5Transport P (Q i)
  have hCpart : IsPartition (fun i => (C i).carrier) P.carrier :=
    section5Transport_partition P Q hP hQpart
  have hlocal (i : Fin M) :
      ∃ m : Nat, ∃ S : Fin m → ModAP N, ∃ z : Fin m → Complex,
        IsPartition (fun j => (S j).carrier) (C i).carrier ∧
        ∀ j, (S j).IsProper ∧ L ≤ (S j).length ∧ ‖z j‖ = 1 ∧
          ∀ x, x ∈ (S j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L) := by
    have hC : (C i).IsProper := section5Transport_isProper P (Q i) hP
      (hQcells i).1 (hQpart.cell_subset i)
    have hlength : (C i).length = H ∨ (C i).length = H + 1 := by
      simpa only [C, section5Transport_length, Nat.add_sub_cancel] using (hQcells i).2.2
    obtain ⟨psi, hpsi, hsplit⟩ := ha ((Q i).start : ZMod N) (p : ZMod N)
    apply quadratic_chunk_phase_localization (C i) phi psi (a * (p : ZMod N) ^ 2)
      hC hpsi hL (by omega) (by omega)
    · simpa only [mul_comm] using hrec.le
    · intro t
      have heq : section5ModIndexPoint (C i) t =
          section5ModIndexPoint P ((Q i).start + t * (p : ZMod N)) := by
        dsimp [C, section5Transport, section5ModIndexPoint, section5IndexPoint]
        rw [hQstep i]
        ring
      rw [heq]
      exact hsplit t
  choose m S z hpart hcells using hlocal
  let e := section5NatFlattenEquiv m
  refine ⟨∑ i, m i, (fun j => let v := e.symm j; S v.1 v.2),
    (fun j => let v := e.symm j; z v.1 v.2), ?_, ?_⟩
  · exact finsetPartition_flatten m (fun i => (C i).carrier) P.carrier
      (fun i j => (S i j).carrier) hCpart hpart
  · intro j
    exact hcells (e.symm j).1 (e.symm j).2

theorem thresholdFreePolynomialLocalization_two : ThresholdFreePolynomialLocalization 2 := by
  intro N _ P phi L hP hphi hL hsize
  exact quadratic_phase_localization P phi hP hphi hL
    ((quadraticLocalization_chunk_budget hL).trans hsize)

/-- The complete degree-two specialization with the catalogue's scale and gain. -/
theorem corollary_5_8_degree_two : Corollary58At 2 :=
  corollary58At_of_threshold_free_localization 2 (by omega) thresholdFreePolynomialLocalization_two

end LeanProofs.GowersSzemeredi
