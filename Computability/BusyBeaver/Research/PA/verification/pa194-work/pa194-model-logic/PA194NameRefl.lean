import PA194GuardedUniversalIntro
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher PA194FormulaDispatcher
section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {T : Theory SourceL} [T.Δ₁]

theorem free_or_neg_self {p : V} (hp : IsSemiformula PA194PAeq.language 1 p) :
    free PA194PAeq.language (neg PA194PAeq.language p ^⋎ p) =
      neg PA194PAeq.language (free PA194PAeq.language p) ^⋎ free PA194PAeq.language p := by
  have hn : IsSemiformula PA194PAeq.language 1 (neg PA194PAeq.language p) := IsSemiformula.neg_iff.mpr hp
  have hw : IsSemitermVec PA194PAeq.language 1 0 (?[^&(0 : V)] : V) := by simp
  show subst PA194PAeq.language (?[^&(0 : V)] : V)
      (shift PA194PAeq.language (neg PA194PAeq.language p ^⋎ p)) = _
  rw [shift_or hn.isUFormula hp.isUFormula, shift_neg hp,
    substs_or (IsSemiformula.neg_iff.mpr hp.shift).isUFormula hp.shift.isUFormula,
    substs_neg hp.shift hw]
  rfl

theorem guarded_tr_em (p : V) (hp : IsSemiformula PA194PAeq.language 0 p) :
    GDerivable T ({tr (neg PA194PAeq.language p ^⋎ p)} : V) := by
  let A : V := tr p
  let B : V := neg SourceL A ^⋎ A
  have hA : IsFormula SourceL A := tr_valid hp
  have hN : IsFormula SourceL (neg SourceL A) := IsSemiformula.neg_iff.mpr hA
  have hB : IsFormula SourceL B := IsSemiformula.or.mpr ⟨hN,hA⟩
  have hs : IsFormulaSet SourceL (insert (neg SourceL A) (insert A ({B} : V))) := by
    rw [singleton_eq_insert]
    exact fs_cons hN (fs_cons hA (fs_cons hB fs_nil))
  have he : GDerivable T (insert (neg SourceL A) (insert A ({B} : V))) :=
    GDerivable.em hs A (by simp) (by simp)
  have hh : GDerivable T ({B} : V) := GDerivable.or_m (by simp [B]) he
  rw [tr_or (IsSemiformula.neg_iff.mpr hp) hp, tr_neg hp]
  exact hh

theorem nRefl (s : V) (hs : IsSemiterm PA194PAeq.language 0 s) :
    GDerivable T (insert (tr (nameAll s s)) (∅ : V)) := by
  let p : V := peq (^#(0 : V)) (termBShift PA194PAeq.language s)
  have hp : IsSemiformula PA194PAeq.language 1 p :=
    peq_valid (by simp) (bShift_valid hs)
  have hb : IsSemiformula PA194PAeq.language 1 (neg PA194PAeq.language p ^⋎ p) :=
    IsSemiformula.or.mpr ⟨IsSemiformula.neg_iff.mpr hp,hp⟩
  have hh := guarded_tr_em (T := T) (free PA194PAeq.language p) hp.free
  have hout := guarded_tr_all_intro (T := T) hb (by simpa only [free_or_neg_self hp] using hh)
  simpa only [singleton_eq_insert,nameAll,p] using hout
#print axioms free_or_neg_self
#print axioms guarded_tr_em
#print axioms nRefl
end generic
end PA194GuardedCompiler
