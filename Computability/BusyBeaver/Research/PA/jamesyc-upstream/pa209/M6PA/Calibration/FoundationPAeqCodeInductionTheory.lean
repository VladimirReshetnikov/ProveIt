module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionRecognizer
@[expose] public section
/-! Both directions of quotation calibration against exactly universally closed
successor induction formulas, with the canonical closure arity proved. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem paeq_fvarVec_val_eq (m : ℕ) :
    fvarVec ((m : ℕ) : V)
      = SemitermVec.val
          (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V Presentation.language 0)) := by
  apply nth_ext (by simp)
  intro i hi
  rw [len_fvarVec] at hi
  obtain ⟨j, rfl⟩ := eq_nat_of_lt_nat hi
  have hj : j < m := by exact_mod_cast hi
  rw [nth_fvarVec _ _ hi, show ((j : ℕ) : V) = ((⟨j, hj⟩ : Fin m) : ℕ) from rfl,
    SemitermVec.val_nth_eq
      (fun i : Fin m ↦ (Semiterm.fvar (↑(i : ℕ)) : Bootstrapping.Semiterm V Presentation.language 0)) ⟨j, hj⟩]
  simp

theorem paeq_subst_fvarVec_quote {m : ℕ} (β : Semiproposition Presentation.language m) :
    Bootstrapping.subst Presentation.language (fvarVec ((m : ℕ) : V)) (⌜β⌝ : V)
      = (⌜(β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm Presentation.language)))⌝ : V) := by
  rw [paeq_fvarVec_val_eq]
  change ((⌜β⌝ : Bootstrapping.Semiformula V Presentation.language m).subst _).val
    = (⌜β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm Presentation.language))⌝ : Bootstrapping.Semiformula V Presentation.language 0).val
  simp [FirstOrder.Semiformula.typed_quote_substs, Semiterm.typed_quote_fvar]

def targetInductionTheory : Theory Presentation.language :=
  fun σ => ∃p : Semiproposition Presentation.language 1, (Presentation.inductionFormula p).univCl=σ
theorem targetInduction_quote_iff (φ : Semiproposition Presentation.language 0) :
    targetInductionR (⌜φ⌝ : Nat) ↔ ∃ σ ∈ targetInductionTheory, φ = σ := by
  constructor;
  · rintro ⟨m, -, b, -, hp, hU, hsh, hbv, K, -, hK, hsubst⟩;
    obtain ⟨γ, rfl⟩ := IsSemiformula.sound hK;
    obtain ⟨β, rfl⟩ := IsSemiformula.sound (hbv ▸ hU.isSemiformula);
    have hβγ : β ⇜ (fun i : Fin m ↦ (&↑i : SyntacticTerm Presentation.language)) = Presentation.inductionFormula γ :=
      (Semiformula.quote_inj_iff (V := ℕ)).mp <| by
        simpa [hsubst, targetIndBody_quote] using (paeq_subst_fvarVec_quote (V := ℕ) β).symm;
    have hφ : φ = ∀¹* β := (Semiformula.quote_inj_iff (V := ℕ)).mp <| by
      simp [hp, quote_allClosure];
    have hfree : β.freeVariables = ∅ := Semiformula.freeVariables_eq_empty_of_shift_eq <|
      (Semiformula.quote_inj_iff (V := ℕ)).mp <| by rw [Semiformula.quote_shift]; exact hsh;
    use (Presentation.inductionFormula γ).univCl;
    and_intros;
    · exact ⟨γ, rfl⟩;
    · simp [hφ, paeq_allClosure_eq_univCl' β hfree hbv, hβγ];
  · rintro ⟨_, ⟨ψ, rfl⟩, rfl⟩;
    set χ := Presentation.inductionFormula ψ;
    have hs : subst Presentation.language (fvarVec (0 + χ.fvSup : ℕ))
        (⌜(Rew.fixitr 0 χ.fvSup ▹ χ : Semiproposition Presentation.language (0 + χ.fvSup))⌝ : ℕ)
          = targetIndBody (⌜ψ⌝ : ℕ) := by
      simpa [quote_subst_fvar_fixitr, targetIndBody_quote]
        using paeq_subst_fvarVec_quote (V := ℕ) (Rew.fixitr 0 χ.fvSup ▹ χ);
    rw [Semiformula.coe_univCl_eq_univCl', quote_univCl', natCast_nat];
    exact ⟨_, index_le_qqAlls _ _, _, le_qqAlls _ _, rfl,
      (Semiformula.quote_isSemiformula _).isUFormula, quote_shift_fixitr χ,
      (bv_quote_fixitr χ).trans (zero_add _).symm, ⌜ψ⌝, by rw [hs]; exact le_targetIndBody _,
      by simp, hs⟩;

noncomputable instance targetInductionTheory_delta1 : targetInductionTheory.Δ₁ where
  ch := targetInductionCh
  mem_iff φ := by simpa using targetInduction_quote_iff φ
  isDelta1 := Bounding.HierarchySymbol.Semiformula.ProvablyProperOn.arithmetic_ofProperOn.{0} _
    fun V _ _ => targetInductionR_defined.proper

#print axioms paeq_fvarVec_val_eq
#print axioms paeq_subst_fvarVec_quote
#print axioms targetInduction_quote_iff
#print axioms targetInductionTheory_delta1
end M6.PA.FoundationPAeqCode

