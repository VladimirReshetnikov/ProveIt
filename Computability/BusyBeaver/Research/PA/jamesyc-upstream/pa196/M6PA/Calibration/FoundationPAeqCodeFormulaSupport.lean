module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeAtomSupport
@[expose] public section
/-! Exact formula support preservation, including the extra strict-order binder.
This is an arbitrary-model syntax induction, not standard quotation. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem atomCode_bv (param : V) {k r ts : V} (hr : (ℒₒᵣ).IsRel k r)
    (ht : IsUTermVec ℒₒᵣ k ts) :
    bv Presentation.language (atomCode param k r ts)=listMax (termBVVec ℒₒᵣ k ts) := by
  obtain ⟨rfl,hr'⟩ := (original_relations _ _).mp hr
  obtain ⟨s,t,rfl⟩ := eq_doubleton_of_len_eq_two.mp ht.lh.symm
  have hs : IsUTerm ℒₒᵣ s := by simpa using (ht.nth (i:=0) (by simp))
  have ht' : IsUTerm ℒₒᵣ t := by simpa using (ht.nth (i:=1) (by simp))
  have hss := termCode_isUTerm hs
  have htt := termCode_isUTerm ht'
  rcases hr' with rfl|rfl <;>
    simp [atomCode,equality_bv,less_bv,hss,htt,termCode_bv,hs,ht']

theorem formulaCode_bv (param : V) {p : V} (hp : IsUFormula ℒₒᵣ p) :
    bv Presentation.language (formulaCode param p)=bv ℒₒᵣ p := by
  apply IsUFormula.induction1 𝚺 (P:=fun p=>bv Presentation.language (formulaCode param p)=bv ℒₒᵣ p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · definability
  · intro k r ts hr ht
    rw [formulaCode_rel _ _ _ _ hr ht,bv_rel hr ht,atomCode_bv param hr ht]
  · intro k r ts hr ht
    rw [formulaCode_nrel _ _ _ _ hr ht,(atom_valid param hr ht.isSemitermVec).isUFormula.bv_neg,
      bv_nrel hr ht,atomCode_bv param hr ht]
  · simp [formulaCode_verum,formulaCode_falsum]
  · simp [formulaCode_verum,formulaCode_falsum]
  · intro p q hp hq ihp ihq
    rw [formulaCode_and _ _ _ hp hq,bv_and (formulaCode_isUFormula param hp) (formulaCode_isUFormula param hq),bv_and hp hq,ihp,ihq]
  · intro p q hp hq ihp ihq
    rw [formulaCode_or _ _ _ hp hq,bv_or (formulaCode_isUFormula param hp) (formulaCode_isUFormula param hq),bv_or hp hq,ihp,ihq]
  · intro p hp ih
    rw [formulaCode_all _ _ hp,bv_all (formulaCode_isUFormula param hp),bv_all hp,ih]
  · intro p hp ih
    rw [formulaCode_exs _ _ hp,bv_ex (formulaCode_isUFormula param hp),bv_ex hp,ih]

#print axioms atomCode_bv
#print axioms formulaCode_bv
end M6.PA.FoundationPAeqCode

