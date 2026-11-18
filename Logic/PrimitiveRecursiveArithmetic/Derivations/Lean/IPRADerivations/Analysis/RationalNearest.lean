import IPRADerivations.Analysis.RationalHausdorff

/-!
# The actual least nearest-neighbor program on original rational lists

Finite-demand `thm:aggregate-chain` needs a fixed finite selector, rather
than an existential cover witness. Normalize the actual pool of the two
lists, perform its least argmin, and retain that numerical index in the
original target list. The radius theorem returns one selected index for
every coordinate, including unreduced independently denominated inputs.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalNearest

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.RationalHausdorff
open LeanProofs.IPRA.Analysis.RationalSupMetric (metricF)
open LeanProofs.IPRA.Foundations
open LeanProofs.IPRA.Foundations.FiniteHausdorff
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def selected (S T d i : PTm n) : PTm n :=
  nearest metricF (entry (grid .left S T d) i) (grid .right S T d) (parameter S T d)

@[simp] theorem subst_selected {m : ℕ} (σ : Fin n → PTm m) (S T d i : PTm n) :
    Syn.subst σ (selected S T d i) =
      selected (Syn.subst σ S) (Syn.subst σ T) (Syn.subst σ d) (Syn.subst σ i) := by
  simp only [selected, subst_nearest, MasterCertificate.subst_entry, subst_grid, subst_parameter]

/-- The selected index belongs to the original target list. The program is
total even on empty targets, but this useful range assertion retains its guard. -/
theorem selected_spec (S T d i : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] lt (selected S T d i) (length T) := by
  have positive := le_congr (.eqRefl _) (grid_length .right S T d).eqSymm hT
  exact lt_congr (.eqRefl _) (grid_length .right S T d)
    (Prf.andE₁ (nearest_spec metricF _ _ _ positive))

theorem selected_distance (S T d i : PTm n) (hT : Γ ⊢[PRAAx] le one (length T)) :
    Γ ⊢[PRAAx] distance metricF (entry (grid .left S T d) i)
      (entry (grid .right S T d) (selected S T d i)) (parameter S T d) ≐
        distanceTo metricF (entry (grid .left S T d) i) (grid .right S T d) (parameter S T d) :=
  Prf.andE₂ (nearest_spec metricF _ _ _
    (le_congr (.eqRefl _) (grid_length .right S T d).eqSymm hT))

/-- A finite hit is consumed and its local witness sealed. The returned
index is the actual least argmin, rather than the input existential witness. -/
theorem selected_radius (S T d i A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (hit : Γ ⊢[PRAAx] originalHit .left .right S T d A B i) :
    Γ ⊢[PRAAx] pointRadius (entry S i) (entry T (selected S T d i)) d A B := by
  have minimum := minimum_bound_of_original_hit .left .right S T d i A B hi hit
  have bound := le_congr (congrMul (.eqRefl _) (selected_distance S T d i hT)).eqSymm
    (.eqRefl _) minimum
  exact metric_to_point_radius .left .right S T d i (selected S T d i) A B
    hi (selected_spec S T d i hT) bound

theorem cover_selected_radius (S T d i A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length S)) (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] originalClose S T d A B) :
    Γ ⊢[PRAAx] pointRadius (entry S i) (entry T (selected S T d i)) d A B :=
  selected_radius S T d i A B hi hT
    (originalCover_at .left .right S T d A B i (Prf.andE₁ h) hi)

/-- Every supplied original candidate bounds the actual selected point. -/
theorem candidate_radius (S T d i j A B : PTm n)
    (hi : Γ ⊢[PRAAx] lt i (length S)) (hj : Γ ⊢[PRAAx] lt j (length T))
    (hT : Γ ⊢[PRAAx] le one (length T))
    (h : Γ ⊢[PRAAx] pointRadius (entry S i) (entry T j) d A B) :
    Γ ⊢[PRAAx] pointRadius (entry S i) (entry T (selected S T d i)) d A B :=
  selected_radius S T d i A B hi hT (originalHit_intro .left .right S T d A B i j hj h)

/-- Equal normalized scores are resolved by the least original target index. -/
theorem selected_least (S T d i j : PTm n)
    (hj : Γ ⊢[PRAAx] lt j (length T))
    (tie : Γ ⊢[PRAAx] distance metricF (entry (grid .left S T d) i)
      (entry (grid .right S T d) j) (parameter S T d) ≐
      distance metricF (entry (grid .left S T d) i)
      (entry (grid .right S T d) (selected S T d i)) (parameter S T d)) :
    Γ ⊢[PRAAx] le (selected S T d i) j := by
  have bound := index_le_pred (lt_congr (.eqRefl _) (grid_length .right S T d).eqSymm hj)
  apply ApproximateWitness.argmin_tie (score metricF) bound
  exact (score_at metricF _ _ _ j).eqTrans (tie.eqTrans (score_at metricF _ _ _ _).eqSymm)

def selectedF : PR 4 := PTm.toPR (selected (var 0) (var 1) (var 2) (var 3))

theorem selected_at (S T d i : PTm n) :
    Γ ⊢[PRAAx] FiniteQueryDemand.apply4 selectedF S T d i ≐ selected S T d i := by
  have h := toPR_eq (Γ := Γ) (selected (var 0) (var 1) (var 2) (var 3) : PTm 4) ![S,T,d,i]
  simpa only [selectedF, FiniteQueryDemand.apply4, subst_selected, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] using h

theorem selected_program_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (FiniteQueryDemand.apply4 selectedF (var 0) (var 1) (var 2) (var 3) ≐
        selected (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (selected_at _ _ _ _)

theorem selected_range_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le one (length (var 1)) ⟶
        lt (FiniteQueryDemand.apply4 selectedF (var 0) (var 1) (var 2) (var 3)) (length (var 1))) :=
  closeUniv 4 (.impI (lt_congr (selected_at _ _ _ _).eqSymm (.eqRefl _) (selected_spec _ _ _ _ Prf.hyp0)))

theorem selected_radius_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (lt (var 3) (length (var 0)) ⟶ le one (length (var 1)) ⟶
        originalHit .left .right (var 0) (var 1) (var 2) (var 4) (var 5) (var 3) ⟶
        pointRadius (entry (var 0) (var 3))
          (entry (var 1) (selected (var 0) (var 1) (var 2) (var 3))) (var 2) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (selected_radius _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

theorem cover_selected_radius_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (lt (var 3) (length (var 0)) ⟶ le one (length (var 1)) ⟶
        originalClose (var 0) (var 1) (var 2) (var 4) (var 5) ⟶
        pointRadius (entry (var 0) (var 3))
          (entry (var 1) (selected (var 0) (var 1) (var 2) (var 3))) (var 2) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (.impI (cover_selected_radius _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.RationalNearest
