import GowersSzemeredi.Proofs05FiniteChunkLocalization
import GowersSzemeredi.Proofs05QuadraticLocalization

/-! Complete threshold-free polynomial phase localization by induction on
its degree, then discharge the full catalogue statement of Corollary 5.8. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem thresholdFreePolynomialLocalization_succ {k : Nat} (hk : 2 ≤ k)
    (hloc : ThresholdFreePolynomialLocalization k) : ThresholdFreePolynomialLocalization (k + 1) := by
  classical
  intro N _ P phi L hP hphi hL hsize
  let H := finiteLocalizationChunk k L
  let R := finiteLocalizationPrecision (k + 1) L H
  let T := finiteRecurrenceSample (k + 1) R
  have hH : 1 ≤ H := (finiteLocalizationChunk_bounds (k := k) hL).1
  have hR : 2 ≤ R := finiteLocalizationPrecision_ge_two hL hH
  have hbudget : T * (H + 1) ^ 2 ≤ P.length :=
    (finiteLocalization_chunk_budget hk hL).trans hsize
  have hT : T ≤ P.length := by
    calc
      T = T * 1 := (Nat.mul_one T).symm
      _ ≤ T * (H + 1) ^ 2 := Nat.mul_le_mul_left T (one_le_pow₀ (by omega))
      _ ≤ _ := hbudget
  have hPN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  let f : ZMod N → ZMod N := fun x => phi (section5ModIndexPoint P x)
  have hf : PolynomialOn (k + 1) Finset.univ f := polynomialOn_section5ModIndexPoint P phi hphi
  obtain ⟨a, ha⟩ := polynomialOn_affine_degree_drop f hf
  obtain ⟨p, hp, hpT, hrec⟩ := polynomial_recurrence_finite a (by omega : 2 ≤ k + 1) hR (hT.trans hPN)
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
    apply polynomial_chunk_phase_localization hloc (C i) phi psi (a * (p : ZMod N) ^ (k + 1))
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

theorem thresholdFreePolynomialLocalization_all :
    ∀ k : Nat, 1 ≤ k → ThresholdFreePolynomialLocalization k := by
  intro k
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        exact thresholdFreePolynomialLocalization_one
      by_cases hk1 : k = 1
      · subst k
        exact thresholdFreePolynomialLocalization_two
      exact thresholdFreePolynomialLocalization_succ (by omega) (ih (by omega))

/-- Corollary 5.8 with its full catalogue type, in every positive degree. -/
theorem corollary_5_8_holds : corollary_5_8 :=
  corollary_5_8_holds_of_threshold_free_localization thresholdFreePolynomialLocalization_all

end LeanProofs.GowersSzemeredi
