import GowersSzemeredi.Proofs05ThresholdFreeCorollary
import GowersSzemeredi.Proofs05AffineLocalizationScale
import GowersSzemeredi.Proofs02Partition
import GowersSzemeredi.Proofs05Downstream

/-! The affine base of threshold-free phase localization. Lemma 2.3 gives
the required proper cells directly; target-minus-one refinement is unnecessary
when the conclusion only asks for a lower bound on every cell length. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem affine_phase_localization {N L : Nat} [NeZero N]
    (P : ModAP N) (phi : ZMod N → ZMod N) (hP : P.IsProper)
    (hphi : PolynomialOn 1 Finset.univ phi) (hL : 2 ≤ L)
    (hsize : 1024 * L ^ 3 ≤ P.length) :
    ∃ m : Nat, ∃ R : Fin m → ModAP N, ∃ z : Fin m → Complex,
      IsPartition (fun j => (R j).carrier) P.carrier ∧
      ∀ j, (R j).IsProper ∧ L ≤ (R j).length ∧ ‖z j‖ = 1 ∧
        ∀ x, x ∈ (R j).carrier → ‖exponential (-(phi x)) - z j‖ ≤ 1 / (4 * L) := by
  classical
  have hrN : P.length ≤ N := by
    rw [← hP]
    simpa only [ZMod.card] using P.carrier.card_le_univ
  have hr : 0 < P.length := by
    have hp : 0 < 1024 * L ^ 3 := by positivity
    omega
  obtain ⟨s, hs, hsN, hrs, hlen, herror⟩ :=
    affine_localization_diameter_scale (NeZero.pos N) hL hsize hrN
  have hlin : NatToZModLinear P.length (fun x => phi (section5IndexPoint P x)) := by
    obtain ⟨c, hc⟩ := polynomialOn_section5ModIndexPoint P phi hphi
    refine ⟨c 1, c 0, ?_⟩
    intro x hx
    simpa [Fin.sum_univ_two, section5_modIndexPoint_natCast, add_comm] using
      hc (x : ZMod N) (Finset.mem_univ _)
  obtain ⟨m, Q, hQpart, hQcells⟩ := lemma_2_3_holds N P.length s (NeZero.pos N)
    hr hs hrN hsN hrs _ hlin
  choose a ha using fun j => (hQcells j).2.1
  refine ⟨m, fun j => section5Transport P (Q j), fun j => exponential (-(a j)),
    section5Transport_partition P Q hP hQpart, ?_⟩
  intro j
  have hsub : (Q j).carrier ⊆ Finset.range P.length := hQpart.cell_subset j
  refine ⟨section5Transport_isProper P (Q j) hP (hQcells j).1 hsub,
    ?_, AddChar.norm_apply (ZMod.stdAddChar (N := N)) _, ?_⟩
  · exact_mod_cast hlen.trans (hQcells j).2.2.1
  · intro x hx
    rw [section5Transport_carrier] at hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
    exact (downstream_phase_close_of_mem_interval (a j) _
      (ha j (Finset.mem_image.mpr ⟨t, ht, rfl⟩))).trans herror

theorem thresholdFreePolynomialLocalization_one : ThresholdFreePolynomialLocalization 1 := by
  intro N _ P phi L hP hphi hL hsize
  have hs : (2 * L) ^ 8 ≤ P.length := by
    have hK : polynomialPartitionConstant 1 / 2 = 8 := by norm_num [polynomialPartitionConstant]
    simpa only [hK] using hsize
  exact affine_phase_localization P phi hP hphi hL
    ((affine_localization_eighth_power_budget hL).trans hs)

/-- The complete degree-one specialization, without any added scale condition. -/
theorem corollary_5_8_degree_one : Corollary58At 1 :=
  corollary58At_of_threshold_free_localization 1 (by omega) thresholdFreePolynomialLocalization_one

end LeanProofs.GowersSzemeredi
