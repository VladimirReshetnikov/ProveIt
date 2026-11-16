module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaFreeSupportLaws
@[expose] public section
namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => Presentation.language

theorem freeSupported_subst {s r l w p : V} (hp : IsSemiformula L s p)
    (hw : IsSemitermVec L s r w) (hs : FreeSupported l p)
    (hws : ∀ i<s, NumericPAeqTerm.FreeSupported l (nth w i)) : FreeSupported l (subst L w p) := by
  have hall : ∀ {s p w : V}, IsSemiformula L s p → IsUTermVec L s w →
      (∀ i<s, NumericPAeqTerm.FreeSupported l (nth w i)) → FreeSupported l p → FreeSupported l (subst L w p) := by
    apply semiformula_subst_induction (P:=fun s w p q => IsUTermVec L s w →
      (∀ i<s, NumericPAeqTerm.FreeSupported l (nth w i)) → FreeSupported l p → FreeSupported l q)
    · dsimp [FreeSupported,NumericPAeqTerm.FreeSupported]; definability
    · intro n w k r ts hr ht hw hws hs
      apply (freeSupported_rel hr (hw.isSemitermVec.termSubstVec ht).isUTerm).mpr
      intro i hi
      rw [nth_termSubstVec ht.isUTerm hi]
      exact NumericPAeqTerm.freeSupported_subst (ht.nth hi) hw.isSemitermVec
        ((freeSupported_rel hr ht.isUTerm).mp hs i hi) hws
    · intro n w k r ts hr ht hw hws hs
      apply (freeSupported_nrel hr (hw.isSemitermVec.termSubstVec ht).isUTerm).mpr
      intro i hi
      rw [nth_termSubstVec ht.isUTerm hi]
      exact NumericPAeqTerm.freeSupported_subst (ht.nth hi) hw.isSemitermVec
        ((freeSupported_nrel hr ht.isUTerm).mp hs i hi) hws
    · intro n w hw hws hs; exact hs
    · intro n w hw hws hs; exact hs
    · intro n w p q hp hq ihp ihq hw hws hs
      apply (freeSupported_and (hp.subst hw.isSemitermVec).isUFormula (hq.subst hw.isSemitermVec).isUFormula).mpr
      have hh := (freeSupported_and hp.isUFormula hq.isUFormula).mp hs
      exact ⟨ihp hw hws hh.1,ihq hw hws hh.2⟩
    · intro n w p q hp hq ihp ihq hw hws hs
      apply (freeSupported_or (hp.subst hw.isSemitermVec).isUFormula (hq.subst hw.isSemitermVec).isUFormula).mpr
      have hh := (freeSupported_or hp.isUFormula hq.isUFormula).mp hs
      exact ⟨ihp hw hws hh.1,ihq hw hws hh.2⟩
    · intro n w p hp ih hw hws hs
      have hh := NumericPAeqTerm.vectorFreeSupported_qVec (show NumericPAeqTerm.VectorFreeSupported l n w from ⟨hw,hws⟩)
      apply (freeSupported_all (hp.subst hw.isSemitermVec.qVec).isUFormula).mpr
      exact ih hh.1 hh.2 ((freeSupported_all hp.isUFormula).mp hs)
    · intro n w p hp ih hw hws hs
      have hh := NumericPAeqTerm.vectorFreeSupported_qVec (show NumericPAeqTerm.VectorFreeSupported l n w from ⟨hw,hws⟩)
      apply (freeSupported_exs (hp.subst hw.isSemitermVec.qVec).isUFormula).mpr
      exact ih hh.1 hh.2 ((freeSupported_exs hp.isUFormula).mp hs)
  exact hall hp hw.isUTerm hws hs
#print axioms freeSupported_subst
end M6.PA.NumericPAeqFormula

