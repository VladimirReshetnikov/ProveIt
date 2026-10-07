import GowersSzemeredi.Proofs18LocalDiscrepancyTransport

/-! Assemble refinements on selected partition cells, leaving the remaining
cells intact. The count budget and discrepancy are summed exactly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Local discrepancy on selected cells gives a global refinement. The
unselected cells require only a budget of one and no discrepancy hypothesis. -/
theorem selected_discrepancy_refinement {N M : Nat} [NeZero N]
    (P : Fin M → ModAP N) (f : ZMod N → Complex) (B : Finset (Fin M))
    (budget : Fin M → Real) (beta : Real)
    (hP : IsPartition (fun i => (P i).carrier) Finset.univ)
    (hproper : ∀ i, (P i).IsProper) (hbudget : ∀ i, 1 ≤ budget i)
    (hlocal : ∀ i ∈ B, ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) (P i).carrier ∧
      (∀ j, (R j).IsProper) ∧ (J : Real) ≤ budget i ∧
      beta * (P i).carrier.card ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖) :
    ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) Finset.univ ∧
      IsRefinement (fun j => (R j).carrier) (fun i => (P i).carrier) ∧
      (∀ j, (R j).IsProper) ∧ (J : Real) ≤ ∑ i, budget i ∧
      beta * (∑ i ∈ B, ((P i).carrier.card : Real)) ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
  classical
  have hexists (i : Fin M) : ∃ J : Nat, ∃ R : Fin J → ModAP N,
      IsPartition (fun j => (R j).carrier) (P i).carrier ∧
      (∀ j, (R j).IsProper) ∧ (J : Real) ≤ budget i ∧
      (if i ∈ B then beta * (P i).carrier.card else 0) ≤ ∑ j, ‖∑ x ∈ (R j).carrier, f x‖ := by
    by_cases hi : i ∈ B
    · simpa only [if_pos hi] using hlocal i hi
    · refine ⟨1, fun _ => P i, ?_, fun _ => hproper i, by simpa using hbudget i, ?_⟩
      · constructor
        · intro x
          simp
        · intro j k hjk
          exact ((bne_iff_ne.mp hjk) (Subsingleton.elim j k)).elim
      · rw [if_neg hi]
        exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  choose J R hpart hRproper hcount hdis using hexists
  refine ⟨∑ i, J i, section5Flatten J R, section5Flatten_partition P J R hP hpart,
    section5Flatten_refinement P J R hP hpart, section5Flatten_isProper J R hRproper, ?_, ?_⟩
  · rw [Nat.cast_sum]
    exact Finset.sum_le_sum fun i _ => hcount i
  · rw [section5Flatten_sum J R (fun Q => ‖∑ x ∈ Q.carrier, f x‖)]
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin M))) => hdis i)
    rw [← Finset.sum_filter] at hs
    have hfilter : Finset.univ.filter (fun i => i ∈ B) = B := by ext i; simp
    rwa [hfilter, ← Finset.mul_sum] at hs

/-- A power count on cells longer than l is bounded by a linear count
weighted by l^(-t). This lets local budgets sum using the exact total mass. -/
theorem rpow_count_le_linear_scale {x l t : Real} (hl : 0 < l) (hlx : l ≤ x)
    (ht : 0 ≤ t) : x ^ (1 - t) ≤ x / l ^ t := by
  have hx : 0 < x := hl.trans_le hlx
  rw [Real.rpow_sub hx, Real.rpow_one]
  exact div_le_div_of_nonneg_left hx.le (Real.rpow_pos_of_pos hl t)
    (Real.rpow_le_rpow hl.le hlx ht)

/-- The same linear budget includes an unrefined cell when 0 <= t <= 1. -/
theorem one_le_linear_scale {x l t : Real} (hl : 1 ≤ l) (hlx : l ≤ x)
    (ht : t ≤ 1) : 1 ≤ x / l ^ t := by
  have hlpos : 0 < l := lt_of_lt_of_le zero_lt_one hl
  apply (one_le_div (Real.rpow_pos_of_pos hlpos t)).mpr
  have hpow : l ^ t ≤ l := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hl ht
  exact hpow.trans hlx

end LeanProofs.GowersSzemeredi
