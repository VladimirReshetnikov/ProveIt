import PA194NameUniqSubstSecond
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem shift_uniq {t : V} (ht : IsSemiterm PA194PAeq.language 0 t) :
    shift PA194PAeq.language (uniq t) = uniq (termShift PA194PAeq.language t) := by
  have hb : IsSemiterm PA194PAeq.language 2 (termBShift PA194PAeq.language (termBShift PA194PAeq.language t)) := by
    simpa [one_add_one_eq_two] using IsSemiterm.termBShift (bShift_valid ht)
  have h0 : IsSemiterm PA194PAeq.language 2 (^#(0 : V)) := by simp
  have h1 : IsSemiterm PA194PAeq.language 2 (^#(1 : V)) := by simp
  have hq := uniqMatrix_valid ht
  have hinner : IsSemiformula PA194PAeq.language 1 (^∀ (uniqMatrix t)) :=
    IsSemiformula.all.mpr (by simpa [one_add_one_eq_two] using hq)
  have he0 := peq_valid h0 hb
  have he1 := peq_valid h1 hb
  have heq := peq_valid h1 h0
  have hr := IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr he0,heq⟩
  change shift PA194PAeq.language (^∀ (^∀ (uniqMatrix t))) = _
  rw [shift_all hinner.isUFormula, shift_all hq.isUFormula]
  unfold uniqMatrix uniq
  rw [shift_or (IsSemiformula.neg_iff.mpr he1).isUFormula hr.isUFormula,
    shift_neg he1, shift_or (IsSemiformula.neg_iff.mpr he0).isUFormula heq.isUFormula,
    shift_neg he0, shift_peq h1 hb, shift_peq h0 hb, shift_peq h1 h0]
  simp only [termShift_bvar]
  rw [←termBShift_termShift (bShift_valid ht), ←termBShift_termShift ht]
#print axioms shift_uniq
end generic
end PA194GuardedCompiler
