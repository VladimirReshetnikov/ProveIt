module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionBody
@[expose] public section
/-! Exact canonical universal closure, including the non-vacuous arity guard.
Specializes the pinned Foundation argument to the existing PAeq language. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
theorem paeq_allClosure_eq_univCl' {m : ℕ} (β : Semiproposition Presentation.language m)
    (hfree : β.freeVariables = ∅) (hbv : bv Presentation.language (⌜β⌝ : ℕ) = m) :
    (∀¹* β : Semiproposition Presentation.language 0)
      = (β ⇜ fun i : Fin m ↦ (&↑i : SyntacticTerm Presentation.language)).univCl' := by
  obtain ⟨χ, hχ⟩ : ∃ χ, β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm Presentation.language)) = χ := ⟨_, rfl⟩;
  rw [hχ];
  have hcodeβ : (⌜(Rew.fixitr 0 m ▹ χ : Semiproposition Presentation.language (0 + m))⌝ : ℕ) = ⌜β⌝ := by
    have : (Rew.fixitr 0 m ▹ χ : Semiproposition Presentation.language (0 + m))
        = Rew.castLE (Nat.le_add_left m 0) ▹ β := by
      rw [← hχ, ← TransitiveRewriting.comp_app];
      apply Semiformula.rew_eq_of_funEqOn;
      · intro x; simp [Rew.comp_app, Rew.fixitr_fvar, Fin.ext_iff];
      · intro x hx; simp [Semiformula.FVar?, hfree] at hx;
    rw [this, Semiformula.quote_castLE];
  have hfvle : χ.fvSup ≤ m := by
    by_contra! h;
    have hx := Semiformula.fvar?_fvSup_pred χ (by omega);
    rw [← hχ] at hx;
    rcases Semiformula.fvar?_rew hx with (⟨i, hi⟩ | ⟨z, hz, -⟩);
    · have : χ.fvSup - 1 = i := by
        simpa [hχ, Rew.subst_bvar, Semiterm.FVar?, Semiterm.freeVariables_fvar] using hi;
      omega;
    · simp [Semiformula.FVar?, hfree] at hz;
  have hcode : (⌜(Rew.fixitr 0 m ▹ χ : Semiproposition Presentation.language (0 + m))⌝ : ℕ)
      = ⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition Presentation.language (0 + χ.fvSup))⌝ := by
    have : (Rew.fixitr 0 m ▹ χ : Semiproposition Presentation.language (0 + m))
        = Rew.castLE (by omega : 0 + χ.fvSup ≤ 0 + m) ▹ (Rew.fixitr 0 χ.fvSup ▹ χ) := by
      rw [← TransitiveRewriting.comp_app];
      apply Semiformula.rew_eq_of_funEqOn₀;
      intro x hx;
      have := Semiformula.lt_fvSup_of_fvar? hx;
      simp [Rew.comp_app, Rew.fixitr_fvar, this, show x < m by omega];
    rw [this, Semiformula.quote_castLE];
  have hm : m = χ.fvSup := by rw [← hbv, ← hcodeβ, hcode]; exact bv_quote_fixitr χ;
  apply (Semiformula.quote_inj_iff (V := ℕ)).mp;
  rw [quote_allClosure, Semiformula.univCl', quote_allClosure, ← hcodeβ, hcode, hm];
  simp;

#print axioms paeq_allClosure_eq_univCl'
end M6.PA.FoundationPAeqCode

