import GowersSzemeredi.Proofs13InitialProgression

/-! Declarations of `Proofs13InitialProgression` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-! ### Auditing the printed parameter range -/

/-- The statement before its missing hypotheses are restored. -/
private def lemma134Unrepaired : Prop :=
  ∀ (N : Nat) [NeZero N] (S : Section13Context N) (theta : Real),
    0 < theta → ∃ D : Stage134Data N, IsStage134Data S theta D

/-- The full domain with the zero function supplies a context at every
nonzero modulus, so the counterexamples below are not vacuous. -/
private def lemma134FullContext (N : Nat) [NeZero N] : Section13Context N where
  A := Finset.univ
  phi := fun _ => 0
  alpha := 1
  eta := (2 : Real) ^ (-(44 : Int))
  alpha_pos := by norm_num
  alpha_at_most_one := le_rfl
  card_A := by simp [ZMod.card]; ring
  separately_freiman := by
    constructor
    · intro x
      refine ⟨?_, ?_⟩
      · intro y _
        simp
      · intro s t _ _ _ _ _
        simp
    · intro y
      refine ⟨?_, ?_⟩
      · intro x _
        simp
      · intro s t _ _ _ _ _
        simp
  eta_value := rfl
  mostly_respected := by
    have hcount : respectedArrangementCount 8
        (Finset.univ : Finset (Pair N)) (fun _ : Pair N => (0 : ZMod N)) =
        arrangementCount 8 (Finset.univ : Finset (Pair N)) := by
      apply countWhere_congr
      intro R
      constructor
      · exact fun h => h.1
      · intro hR
        refine ⟨hR, ?_⟩
        unfold DArrangement.IsRespected IsAdditiveTuple
        simp
    unfold MostlyRespectsEight
    rw [hcount]
    have heta : 0 ≤ (2 : Real) ^ (-(44 : Int)) := by positivity
    nlinarith

private lemma lemma134_theta_two_q_bound :
    section13QBound 2 < 1 := by
  unfold section13QBound
  rw [zpow_neg, ← div_eq_mul_inv]
  apply (div_lt_one₀ (by positivity : (0 : Real) < 2 ^ 10479)).2
  exact pow_lt_pow_right₀ (by norm_num : (1 : Real) < 2) (by omega)

/-- For `theta = 2`, the asserted positive integer `q` is bounded strictly
below one.  Thus an upper bound on `theta` is genuinely necessary. -/
theorem lemma_13_4_theta_range_counterexample
    (N : Nat) [NeZero N] (S : Section13Context N) :
    ¬ ∃ D : Stage134Data N, IsStage134Data S 2 D := by
  rintro ⟨D, hD⟩
  have hqPos : 0 < D.q := hD.1
  have hqBound : (D.q : Real) ≤ section13QBound 2 := hD.2.2.2.2.1
  have hqOne : (1 : Real) ≤ D.q := by exact_mod_cast hqPos
  linarith [lemma134_theta_two_q_bound]

/-- At modulus one there is no nonzero progression step, independently of
all other data.  This witnesses the missing prime/nontrivial-modulus
hypothesis in the printed statement. -/
theorem lemma_13_4_modulus_one_counterexample
    (S : Section13Context 1) (theta : Real) :
    ¬ ∃ D : Stage134Data 1, IsStage134Data S theta D := by
  rintro ⟨D, hD⟩
  have hstep : D.P.step ≠ 0 := bne_iff_ne.mp hD.2.1
  exact hstep (Subsingleton.elim _ _)

/-- The modulus-one obstruction is nonvacuous even at a positive `theta`
which satisfies the repaired quantitative upper bound. -/
theorem lemma_13_4_modulus_one_concrete_counterexample :
    ∃ S : Section13Context 1,
      0 < (1 / 8 : Real) ∧ (1 / 8 : Real) ≤ S.alpha ^ 32 / 4 ∧
      ¬ ∃ D : Stage134Data 1, IsStage134Data S (1 / 8) D := by
  refine ⟨lemma134FullContext 1, by norm_num, ?_,
    lemma_13_4_modulus_one_counterexample (lemma134FullContext 1) (1 / 8)⟩
  norm_num [lemma134FullContext]

private theorem lemma134Unrepaired_false : ¬ lemma134Unrepaired := by
  intro h
  have hout := h 2 (lemma134FullContext 2) 2 (by norm_num)
  exact lemma_13_4_theta_range_counterexample 2 (lemma134FullContext 2) hout

/-- Lemma 13.4 at any real graph budget above the source bound. In particular,
this uses the fixed printed budget, without replacing it by the actual count
inside the floor formula. -/
theorem lemma_13_4_at_real_graph_bound
    (N : Nat) [NeZero N] (S : Section13Context N) (theta Qbound : Real)
    (hprime : N.Prime) (htheta : 0 < theta) (hthetaBound : theta ≤ S.alpha ^ 32 / 4)
    (hQbound : section13QBound theta ≤ Qbound) :
    ∃ D : Stage134Data N, IsStage134DataAtRealBound S theta Qbound D := by
  obtain ⟨D, _, hD⟩ := lemma134_at_graph_budget N S theta (fun _ => Qbound)
    hprime htheta hthetaBound (fun _ _ hq => hq.trans hQbound)
  exact ⟨D, hD⟩

/-- The fixed-real-budget floor interpretation displayed in Lemma 13.4. -/
theorem lemma_13_4_fixed_real_bound
    (N : Nat) [NeZero N] (S : Section13Context N) (theta : Real)
    (hprime : N.Prime) (htheta : 0 < theta) (hthetaBound : theta ≤ S.alpha ^ 32 / 4) :
    ∃ D : Stage134Data N,
      IsStage134DataAtRealBound S theta (section13QBound theta) D :=
  lemma_13_4_at_real_graph_bound N S theta (section13QBound theta)
    hprime htheta hthetaBound le_rfl

end LeanProofs.GowersSzemeredi
