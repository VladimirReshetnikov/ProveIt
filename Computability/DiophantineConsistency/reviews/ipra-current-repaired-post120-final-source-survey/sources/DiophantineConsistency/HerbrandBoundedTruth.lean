import DiophantineConsistency.HerbrandBoundedSemantics

/-! Relate finite-term semantics to ordinary first-order semantics. -/
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandBoundedTruth
open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.HerbrandBoundedSemantics

theorem bounded_implies_truth {L : Language} {M : Type} [Structure L M]
    (terms : List (SyntacticTerm L)) (e : ℕ → M) (φ : Proposition L)
    (h : boundedEval terms e φ) : φ.Eval ![] e := by
  have main : ∀ ψ : Proposition L, boundedEval terms e ψ → ψ.Eval ![] e := by
    intro ψ
    induction ψ using (measure (fun ψ : Proposition L => logicalSize ψ)).wf.induction with
    | h ψ ih =>
      intro hb
      cases ψ with
      | rel r v => simpa only [boundedEval.eq_1, Semiformula.eval_rel] using hb
      | nrel r v => simpa only [boundedEval.eq_2, Semiformula.eval_nrel] using hb
      | verum => change True; trivial
      | falsum => simp only [boundedEval.eq_4] at hb
      | and p q =>
          rw [boundedEval.eq_5] at hb
          have hp := ih p (by change logicalSize p < logicalSize (Semiformula.and p q); simp [logicalSize]) hb.1
          have hq := ih q (by change logicalSize q < logicalSize (Semiformula.and p q); simp [logicalSize]) hb.2
          change (p.Eval ![] e) ∧ (q.Eval ![] e)
          exact ⟨hp,hq⟩
      | or p q =>
          rw [boundedEval.eq_6] at hb
          rcases hb with hp | hq
          · have h := ih p (by change logicalSize p < logicalSize (Semiformula.or p q); simp [logicalSize]) hp
            change (p.Eval ![] e) ∨ (q.Eval ![] e)
            exact Or.inl h
          · have h := ih q (by change logicalSize q < logicalSize (Semiformula.or p q); simp [logicalSize]) hq
            change (p.Eval ![] e) ∨ (q.Eval ![] e)
            exact Or.inr h
      | all p => rw [boundedEval.eq_7] at hb; exact False.elim hb
      | exs p =>
          rw [boundedEval.eq_8] at hb
          obtain ⟨t,_,ht⟩ := hb
          have hv := ih (p/[t]) (by
            change logicalSize (Rew.subst ![t] ▹ p) < logicalSize (Semiformula.exs p)
            rw [logicalSize_rew]
            simp [logicalSize]) ht
          apply Semiformula.eval_ex.mpr
          refine ⟨Semiterm.val ![] e t, ?_⟩
          have hargs : (Semiterm.val ![] e ∘ ![t]) = ![Semiterm.val ![] e t] := by
            funext i
            exact Fin.cases rfl (fun j => Fin.elim0 j) i
          simpa [Semiformula.eval_substs, hargs, Matrix.constant_eq_singleton] using hv
  exact main φ h

/-- For an open proposition, finite-term and ordinary semantics coincide. -/
theorem bounded_open_iff {L : Language} {M : Type} [Structure L M]
    (terms : List (SyntacticTerm L)) (e : ℕ → M) (φ : Proposition L) (hOpen : φ.Open) :
    boundedEval terms e φ ↔ φ.Eval ![] e := by
  have main : ∀ ψ : Proposition L, ψ.Open → (boundedEval terms e ψ ↔ ψ.Eval ![] e) := by
    intro ψ
    induction ψ using (measure (fun ψ : Proposition L => logicalSize ψ)).wf.induction with
    | h ψ ih =>
      intro ho
      cases ψ with
      | rel r v => simp only [boundedEval.eq_1, Semiformula.eval_rel]
      | nrel r v => simp only [boundedEval.eq_2, Semiformula.eval_nrel]
      | verum => rw [boundedEval.eq_3]; change True ↔ True; rfl
      | falsum => rw [boundedEval.eq_4]; change False ↔ False; rfl
      | and p q =>
          change max p.qr q.qr = 0 at ho
          have hopen := Nat.max_eq_zero_iff.mp ho
          rw [boundedEval.eq_5]
          change (boundedEval terms e p ∧ boundedEval terms e q) ↔
            (p.Eval ![] e ∧ q.Eval ![] e)
          exact and_congr (ih p (by change logicalSize p < logicalSize (Semiformula.and p q); simp [logicalSize]) hopen.1)
            (ih q (by change logicalSize q < logicalSize (Semiformula.and p q); simp [logicalSize]) hopen.2)
      | or p q =>
          change max p.qr q.qr = 0 at ho
          have hopen := Nat.max_eq_zero_iff.mp ho
          rw [boundedEval.eq_6]
          change (boundedEval terms e p ∨ boundedEval terms e q) ↔
            (p.Eval ![] e ∨ q.Eval ![] e)
          exact or_congr (ih p (by change logicalSize p < logicalSize (Semiformula.or p q); simp [logicalSize]) hopen.1)
            (ih q (by change logicalSize q < logicalSize (Semiformula.or p q); simp [logicalSize]) hopen.2)
      | all p => change p.qr + 1 = 0 at ho; omega
      | exs p => change p.qr + 1 = 0 at ho; omega
  exact main φ hOpen

end DiophantineConsistency.HerbrandBoundedTruth
