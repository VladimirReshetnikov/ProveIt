import DiophantineConsistency.HerbrandChiStageContext
import DiophantineConsistency.HerbrandStageSupport
/-! Exact semantics of the selected existential witness at an interactive stage. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandStageBodyEvaluation
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage HerbrandTupleSchedule HerbrandChiStageContext HerbrandStageSupport

/-- Evaluating the stage body at q gives β on `[q,w,y,x,y₀,z,c,v]`. -/
theorem stageBody_eval {M : Type} [Structure language M] (r j : ℕ)
    (β : Semiproposition language 8) (e : ℕ → M) (q : M) :
    (stageBody r j β).Eval ![q] e ↔ β.Eval
      ![q, e (r+3*j+2), e (r+3*j+1), e (r+3*j),
        Semiterm.val ![] e (candidate j 3), Semiterm.val ![] e (candidate j 2),
        Semiterm.val ![] e (candidate j 1), Semiterm.val ![] e (candidate j 0)] e := by
  unfold stageBody
  rw [Semiformula.eval_rew]
  have hb : (Semiterm.val (L := language) ![q] e ∘
      (Rew.subst ![&(r+3*j+2), &(r+3*j+1), &(r+3*j), candidate j 3,
        candidate j 2, candidate j 1, candidate j 0]).q ∘ Semiterm.bvar) =
      ![q, e (r+3*j+2), e (r+3*j+1), e (r+3*j),
        Semiterm.val ![] e (candidate j 3), Semiterm.val ![] e (candidate j 2),
        Semiterm.val ![] e (candidate j 1), Semiterm.val ![] e (candidate j 0)] := by
    funext i
    refine Fin.cases rfl (fun k => ?_) i
    simp only [Function.comp_apply, Rew.q_bvar_succ, Rew.subst_bvar]
    rw [Semiterm.val_bShift]
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    refine Fin.cases rfl (fun k => ?_) k
    exact Fin.cases rfl (fun k => Fin.elim0 k) k
  have hf : (Semiterm.val (L := language) ![q] e ∘
      (Rew.subst ![&(r+3*j+2), &(r+3*j+1), &(r+3*j), candidate j 3,
        candidate j 2, candidate j 1, candidate j 0]).q ∘ Semiterm.fvar) = e := by
    funext i
    simp [Function.comp_def, Rew.q_fvar]
  rw [hb,hf]
/-- After replacing the current challenges, the original parameters and
four candidate values are unchanged. -/
theorem stageBody_updated_eval {M : Type} [Structure language M] (r j : ℕ)
    (β : Semiproposition language 8) (hβ : β.fvSup ≤ r) (e : ℕ → M) (q x y w : M) :
    (stageBody r j β).Eval ![q] (updateChallenges r j e x y w) ↔ β.Eval
      ![q,w,y,x, Semiterm.val ![] e (candidate j 3), Semiterm.val ![] e (candidate j 2),
        Semiterm.val ![] e (candidate j 1), Semiterm.val ![] e (candidate j 0)] e := by
  have he : ∀ i < r+3*j, e i = updateChallenges r j e x y w i := by
    intro i hi
    exact (updateChallenges_before r j e x y w i hi).symm
  rw [stageBody_eval]
  have h0 : updateChallenges r j e x y w (r+3*j) = x := by simp [updateChallenges]
  have h1 : updateChallenges r j e x y w (r+3*j+1) = y := by simp [updateChallenges]
  have h2 : updateChallenges r j e x y w (r+3*j+2) = w := by simp [updateChallenges]
  rw [h0,h1,h2]
  rw [←candidate_unchanged r j 0 e _ he, ←candidate_unchanged r j 1 e _ he,
    ←candidate_unchanged r j 2 e _ he, ←candidate_unchanged r j 3 e _ he]
  apply Semiformula.eval_iff_of_funEqOn
  intro i hi
  have hi' := Semiformula.lt_fvSup_of_fvar? hi
  exact (he i (by omega)).symm
end DiophantineConsistency.HerbrandStageBodyEvaluation
