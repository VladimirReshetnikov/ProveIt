import IPRADerivations.Core.Pairing
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Growth of continued-fraction denominators (`hurwitz_khinchin_ipra`)

For partial quotients `a_j ≥ 1` the denominators of the convergents,
`q₀ = 1`, `q₋₁ = 0`, `q_{j+1} = a_{j+1} q_j + q_{j−1}`, satisfy `q_j ≥ j`
(`hurwitz.tex`). In iPRA the partial quotients are `a_j = a'(j) + 1` for an
arbitrary unary primitive recursive symbol `a'`, so all sequences with `a_j ≥ 1`
are covered, and `j` is a variable of the formula. The proof is induction on `j`
for the invariant `j ≤ q_j ∧ j + 1 ≤ q_j + q_{j−1} ∧ 1 ≤ q_j`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz

open_ipra exports

variable (a' : PR 1) {n : ℕ} {Γ : List (Fm PTm n)}

/-- Step variables: `0 = j`, `1 = q_j`, `2 = q_{j−1}`, `3` unused. -/
abbrev qStep : PTm 4 := succ (ap1 a' (succ (var 0))) * var 1 + var 2

abbrev q (j : PTm n) : PTm n := sim₁ one zero (qStep a') (var 1) j fun _ => zero
abbrev q' (j : PTm n) : PTm n := sim₂ one zero (qStep a') (var 1) j fun _ => zero

variable {a'}

theorem add_le_add {a b c d : PTm n} (h₁ : Γ ⊢[PRAAx] le a b) (h₂ : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] le (a + c) (b + d) := by
  refine le_of_eq_add (d := monus b a + monus d c) ?_
  refine withEq (eq_add_of_le h₁) fun e₁ => withEq (eq_add_of_le h₂) fun e₂ => ?_
  apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

/-- The invariant; variable `0 = j`. -/
abbrev invariant : Fm PTm 1 :=
  le (var 0) (q a' (var 0)) ⋏ (le (succ (var 0)) (q a' (var 0) + q' a' (var 0)) ⋏ le one (q a' (var 0)))

theorem invariant_open : ([] : List (Fm PTm 1)) ⊢[PRAAx] invariant (a' := a') := by
  ipra_ind (⟨le_QF _ _, le_QF _ _, le_QF _ _⟩) [subst_le, subst_sim₁, subst_sim₂]
  · have e₁ := sim₁_zero (Γ := ([] : List (Fm PTm 0))) one zero (qStep a') (var 1)
      (fun _ : Fin 1 => (zero : PTm 0))
    have e₂ := sim₂_zero (Γ := ([] : List (Fm PTm 0))) one zero (qStep a') (var 1)
      (fun _ : Fin 1 => (zero : PTm 0))
    simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at e₁ e₂
    refine .andI (zero_le _) (.andI ?_ ?_)
    · exact le_congr (.eqRefl _) ((add_zero _).eqSymm.eqTrans (congrAdd e₁ e₂).eqSymm) (le_refl _)
    · exact le_congr (.eqRefl _) e₁.eqSymm (le_refl _)
  · have h₁ : [invariant (a' := a')] ⊢[PRAAx] le (var 0) (q a' (var 0)) := .andE₁ Prf.hyp0
    have h₂ : [invariant (a' := a')] ⊢[PRAAx] le (succ (var 0)) (q a' (var 0) + q' a' (var 0)) :=
      .andE₁ (.andE₂ Prf.hyp0)
    have h₃ : [invariant (a' := a')] ⊢[PRAAx] le one (q a' (var 0)) := .andE₂ (.andE₂ Prf.hyp0)
    have e₁ := sim₁_succ (Γ := [invariant (a' := a')]) one zero (qStep a') (var 1)
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0)
    have e₂ := sim₂_succ (Γ := [invariant (a' := a')]) one zero (qStep a') (var 1)
      (fun _ : Fin 1 => (zero : PTm 1)) (var 0)
    simp only [PTm.subst_add, PTm.subst_mul, subst_ap1, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
      Fin.cases_zero, finCases_one, finCases_two] at e₁ e₂
    -- q_{j+1} = (a + 1) q_j + q_{j−1} ≥ q_j + q_{j−1} ≥ j + 1.
    have hq : [invariant (a' := a')] ⊢[PRAAx] le (succ (var 0)) (q a' (succ (var 0))) := by
      refine le_trans h₂ (le_congr (.eqRefl _) e₁.eqSymm (le_of_eq_add
        (d := ap1 a' (succ (var 0)) * q a' (var 0)) ?_))
      ipra_ring
    refine .andI hq (.andI ?_ ?_)
    · refine le_congr ((succ_eq_add_one _).eqSymm) (congrAdd (.eqRefl _) e₂.eqSymm) (add_le_add hq h₃)
    · exact le_trans (le_congr (.eqRefl _) (.eqRefl _) (le_of_eq_add (d := var 0)
        ((succ_eq_add_one _).eqTrans (add_comm _ _)) |> fun h => h)) hq

/-- `q_j ≥ j` for every `j`. -/
abbrev boundFormula : Fm PTm 1 := le (var 0) (q a' (var 0))

theorem denominator_bound : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (boundFormula (a' := a')) :=
  closeUniv 1 (.andE₁ invariant_open)

end LeanProofs.IPRA.DiophantineNumberTheory.Hurwitz
