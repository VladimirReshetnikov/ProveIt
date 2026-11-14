import PA194PAeqAtomTransport
import PA194PAeqFormulaValidity
set_option autoImplicit false
set_option maxHeartbeats 7000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem formulaCode_subst_internal (param : V) {k p w : V}
    (hp : IsSemiformula ℒₒᵣ k p) (hw : IsUTermVec ℒₒᵣ k w) :
    formulaCode param (subst ℒₒᵣ w p) =
      subst PA194PAeq.language (termVector k w) (formulaCode param p) := by
  let c := (Substs.construction (V := V) ℒₒᵣ)
  have hP : 𝚺₁-Relation₄ (fun w n p y : V => IsUTermVec ℒₒᵣ n w →
      formulaCode param y = subst PA194PAeq.language (termVector n w) (formulaCode param p)) := by
    definability
  have hall := c.semiformula_result_induction (L := ℒₒᵣ) hP
  apply hall ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp hw
  · intro n u a r ts hr ht hu
    have hu' := hu.isSemitermVec
    change formulaCode param (qqRel a r (termSubstVec ℒₒᵣ a u ts)) = _
    rw [formulaCode_rel _ _ _ _ hr (hu'.termSubstVec ht).isUTerm,
      formulaCode_rel _ _ _ _ hr ht.isUTerm]
    exact atomCode_subst param hr hu' ht
  · intro n u a r ts hr ht hu
    have hu' := hu.isSemitermVec
    change formulaCode param (qqNRel a r (termSubstVec ℒₒᵣ a u ts)) = _
    rw [formulaCode_nrel _ _ _ _ hr (hu'.termSubstVec ht).isUTerm,
      formulaCode_nrel _ _ _ _ hr ht.isUTerm,
      substs_neg (atom_valid param hr ht) (termVector_valid hu')]
    rw [atomCode_subst param hr hu' ht]
  · intro n u hu
    change formulaCode param qqVerum = _
    rw [formulaCode_verum,substs_verum]
  · intro n u hu
    change formulaCode param qqFalsum = _
    rw [formulaCode_falsum,substs_falsum]
  · intro n u a b ha hb iha ihb hu
    change IsUTermVec ℒₒᵣ n u → formulaCode param (subst ℒₒᵣ u a) = subst PA194PAeq.language (termVector n u) (formulaCode param a) at iha
    change IsUTermVec ℒₒᵣ n u → formulaCode param (subst ℒₒᵣ u b) = subst PA194PAeq.language (termVector n u) (formulaCode param b) at ihb
    change formulaCode param (qqAnd (subst ℒₒᵣ u a) (subst ℒₒᵣ u b)) = _
    rw [formulaCode_and _ _ _ (ha.subst hu.isSemitermVec).isUFormula (hb.subst hu.isSemitermVec).isUFormula,
      formulaCode_and _ _ _ ha.isUFormula hb.isUFormula,
      substs_and (formulaCode_valid param ha).isUFormula (formulaCode_valid param hb).isUFormula,
      iha hu,ihb hu]
  · intro n u a b ha hb iha ihb hu
    change IsUTermVec ℒₒᵣ n u → formulaCode param (subst ℒₒᵣ u a) = subst PA194PAeq.language (termVector n u) (formulaCode param a) at iha
    change IsUTermVec ℒₒᵣ n u → formulaCode param (subst ℒₒᵣ u b) = subst PA194PAeq.language (termVector n u) (formulaCode param b) at ihb
    change formulaCode param (qqOr (subst ℒₒᵣ u a) (subst ℒₒᵣ u b)) = _
    rw [formulaCode_or _ _ _ (ha.subst hu.isSemitermVec).isUFormula (hb.subst hu.isSemitermVec).isUFormula,
      formulaCode_or _ _ _ ha.isUFormula hb.isUFormula,
      substs_or (formulaCode_valid param ha).isUFormula (formulaCode_valid param hb).isUFormula,
      iha hu,ihb hu]
  · intro n u a ha ih hu
    change IsUTermVec ℒₒᵣ (n+1) (qVec ℒₒᵣ u) → formulaCode param (subst ℒₒᵣ (qVec ℒₒᵣ u) a) = subst PA194PAeq.language (termVector (n+1) (qVec ℒₒᵣ u)) (formulaCode param a) at ih
    change formulaCode param (qqAll (subst ℒₒᵣ (qVec ℒₒᵣ u) a)) = _
    have huq : IsUTermVec ℒₒᵣ (n+1) (qVec ℒₒᵣ u) := (hu.isSemitermVec.qVec).isUTerm
    rw [formulaCode_all _ _ (ha.subst hu.isSemitermVec.qVec).isUFormula,
      formulaCode_all _ _ ha.isUFormula,
      substs_all (formulaCode_valid param ha).isUFormula,
      ih huq,termVector_qVec hu]
  · intro n u a ha ih hu
    change IsUTermVec ℒₒᵣ (n+1) (qVec ℒₒᵣ u) → formulaCode param (subst ℒₒᵣ (qVec ℒₒᵣ u) a) = subst PA194PAeq.language (termVector (n+1) (qVec ℒₒᵣ u)) (formulaCode param a) at ih
    change formulaCode param (qqExs (subst ℒₒᵣ (qVec ℒₒᵣ u) a)) = _
    have huq : IsUTermVec ℒₒᵣ (n+1) (qVec ℒₒᵣ u) := (hu.isSemitermVec.qVec).isUTerm
    rw [formulaCode_exs _ _ (ha.subst hu.isSemitermVec.qVec).isUFormula,
      formulaCode_exs _ _ ha.isUFormula,
      substs_ex (formulaCode_valid param ha).isUFormula,
      ih huq,termVector_qVec hu]

theorem formulaCode_subst (param : V) {k n w p : V}
    (hp : IsSemiformula ℒₒᵣ k p) (hw : IsSemitermVec ℒₒᵣ k n w) :
    formulaCode param (subst ℒₒᵣ w p) =
      subst PA194PAeq.language (termVector k w) (formulaCode param p) :=
  formulaCode_subst_internal param hp hw.isUTerm

#print axioms formulaCode_subst
#print axioms formulaCode_subst_internal
end PA194PAeqTermBlueprint
