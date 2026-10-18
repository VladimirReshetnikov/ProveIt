import GowersSzemeredi.Proofs13FejerArrangementRegularity
import GowersSzemeredi.Proofs13FejerSelection

/-! Arrangement-specific Fejer purification with an explicit score
budget. All structural and counting hypotheses are discharged; the remaining
input is the displayed scalar inequality selecting the kernel length. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem section13_fejer_purification_score {N L M : Nat} [NeZero N] [Fact N.Prime]
    (hL : 2 ≤ L) (hML : 2 * M ≤ L) (hLN : L ≤ N)
    (U : Finset (Pair N)) (phi : Pair N → ZMod N)
    (eta mass : Real) (heta : 0 < eta) (hmass : 0 < mass)
    (hbudget : eta * mass ≤
      eta * (respectedArrangementCount 8 U phi : Real) *
        ((((L : Real) ^ 2)⁻¹) ^ 32 * (M : Real) ^ 33) -
      (arrangementCount 8 U : Real) * ((L : Real)⁻¹) ^ 32 -
      (2 * (L : Real)) ^ 32 * (2 * (N : Real) ^ 31)) :
    ∃ S ⊆ U, mass ≤ (respectedArrangementCount 8 S phi : Real) ∧
      (arrangementCount 8 S : Real) ≤ (1 + eta) * (respectedArrangementCount 8 S phi : Real) := by
  classical
  have hpart (T : Finset (Pair N)) :=
    fejerArrangementEdges_partition_card T (fun R => R.IsRespected phi)
  have he : ((fejerExceptionalArrangements (N := N) (L := L)).card : Real) ≤
      (2 * (L : Real)) ^ 32 * (2 * (N : Real) ^ 31) := by
    exact_mod_cast fejerExceptionalArrangements_card
  obtain ⟨S, hS, hmassS, hbadS⟩ := exists_subset_fejer_purification (by omega : 0 < L) hML U
    (fejerArrangementEdges U (fun R => R.IsRespected phi))
    (fejerArrangementEdges U (fun R => ¬ R.IsRespected phi)) (fejerExceptionalArrangements (L := L))
    (fun R => fejerArrangementVertex R.1) phi (fun z => z.1 * z.2)
    (fun _ => fejerArrangementPositive) (fejerArrangementEdges_carrier U _)
    (fejerArrangementEdges_carrier U _)
    (fun R hR => by
      simp_rw [fejerArrangementPositive_coefficient]
      exact (fejerArrangement_respected_iff R.1 phi).mp (Finset.mem_filter.mp hR).2.2)
    (fun R _ => by
      simp_rw [fejerArrangementPositive_coefficient]
      exact fejerArrangement_feature_sum R.1 R.2)
    (fun R _ hr => fejerArrangement_regular_injective hL R hr)
    (fun R hR hr => fejerArrangement_regular_diagonal hLN R phi hr (by
      simp [fejerArrangementEdges] at hR
      exact hR.2))
    eta mass heta hmass (by
      simp only [show Fintype.card (Option (Fin 15) × Bool) = 32 by decide,
        fejerArrangementEdges_good_card]
      refine hbudget.trans ?_
      gcongr
      exact (Nat.le_add_left _ _).trans_eq (hpart U))
  simp only [fejerArrangementEdges_restrict U S hS, fejerArrangementEdges_good_card] at hmassS hbadS
  refine ⟨S, hS, hmassS, ?_⟩
  rw [← hpart S, fejerArrangementEdges_good_card]
  push_cast
  linarith

end LeanProofs.GowersSzemeredi
