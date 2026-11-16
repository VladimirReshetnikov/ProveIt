module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqFormulaSourceFreeOperation
@[expose] public section

namespace M6.PA.NumericPAeqFormula
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open NumericPAeqTerm (sourceFree sourceFreeVec)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sourceFreeVec_isSemitermVec {s k ts : V} (h : IsSemitermVec Presentation.language k (s+1) ts) :
    IsSemitermVec Presentation.language k s (sourceFreeVec s k ts) := by
  refine IsSemitermVec.iff.mpr ⟨NumericPAeqTerm.sourceFreeVec_length h.isUTerm,?_⟩
  intro i hi
  rw [NumericPAeqTerm.sourceFreeVec_nth h.isUTerm hi]
  exact NumericPAeqTerm.sourceFree_isSemiterm (h.nth hi)

theorem formulaSourceFree_isSemiformula {s p : V} (h : IsSemiformula Presentation.language (s+1) p) :
    IsSemiformula Presentation.language s (formulaSourceFree s p) := by
  suffices ∀ {n p : V}, IsSemiformula Presentation.language n p → ∀ s, n=s+1 →
      IsSemiformula Presentation.language s (formulaSourceFree s p) from this h s rfl
  intro n p hp
  apply IsSemiformula.pi1_structural_induction (P:=fun n p => ∀s,n=s+1 →
    IsSemiformula Presentation.language s (formulaSourceFree s p)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · definability
  · intro n k r ts hr ht s he
    subst n
    rw [formulaSourceFree_rel _ _ _ _ hr ht.isUTerm]
    exact IsSemiformula.rel.mpr ⟨hr,sourceFreeVec_isSemitermVec ht⟩
  · intro n k r ts hr ht s he
    subst n
    rw [formulaSourceFree_nrel _ _ _ _ hr ht.isUTerm]
    exact IsSemiformula.nrel.mpr ⟨hr,sourceFreeVec_isSemitermVec ht⟩
  · intro n s he; simp
  · intro n s he; simp
  · intro n p q hp hq ihp ihq s he
    rw [formulaSourceFree_and _ _ _ hp.isUFormula hq.isUFormula]
    exact IsSemiformula.and.mpr ⟨ihp s he,ihq s he⟩
  · intro n p q hp hq ihp ihq s he
    rw [formulaSourceFree_or _ _ _ hp.isUFormula hq.isUFormula]
    exact IsSemiformula.or.mpr ⟨ihp s he,ihq s he⟩
  · intro n p hp ih s he
    rw [formulaSourceFree_all _ _ hp.isUFormula]
    exact IsSemiformula.all.mpr (ih (s+1) (by rw [he]))
  · intro n p hp ih s he
    rw [formulaSourceFree_exs _ _ hp.isUFormula]
    exact IsSemiformula.exs.mpr (ih (s+1) (by rw [he]))

#print axioms sourceFreeVec_isSemitermVec
#print axioms formulaSourceFree_isSemiformula
end M6.PA.NumericPAeqFormula

