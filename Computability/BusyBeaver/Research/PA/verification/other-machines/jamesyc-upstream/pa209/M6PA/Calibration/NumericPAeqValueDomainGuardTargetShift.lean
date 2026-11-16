module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueDomainGuardValidity
public import M6PA.Calibration.NumericPAeqTermTargetShiftParameters
@[expose] public section
namespace M6.PA.NumericPAeqValueDomainGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource (language)
open NumericPAeqTerm
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] guardGraph targetShiftTermsGraph
noncomputable def targetShiftInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ env m n, !((isSemitermVec language).sigma) m n env → k≤m →
    ∃ se g sg tg, !targetShiftTermsGraph se env ∧ !guardGraph g env k ∧
      !guardGraph sg se k ∧ !(shiftGraph language) tg g ∧ tg=sg”
theorem targetShift_invariant (k:V) : targetShiftInvariant.Evalb ![k] ↔
    ∀env m n:V,IsSemitermVec language m n env→k≤m→
      shift language (guard env k)=guard (targetShiftTerms env) k := by
  simp [targetShiftInvariant,guard_graph,targetShiftTerms_graph,Matrix.comp_vecCons'']
attribute [local irreducible] targetShiftInvariant
theorem guard_targetShift {env m n k:V} (h:IsSemitermVec language m n env) (hk:k≤m) :
    shift language (guard env k)=guard (targetShiftTerms env) k := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀env m n:V,IsSemitermVec language m n env→k≤m→
      shift language (guard env k)=guard (targetShiftTerms env) k := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀env m n:V,
      IsSemitermVec language m n env→k≤m→shift language (guard env k)=guard (targetShiftTerms env) k) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb targetShiftInvariant,by trivial,?_⟩
      intro k; simpa using (targetShift_invariant (V:=V) k).symm
    · intro env m n h hk; simp
    · intro k ih env m n h hk
      have hkm : k<m := lt_of_lt_of_le (lt_add_one k) hk
      have hprev := guard_isSemiformula env k n (fun i hi=>h.nth (lt_trans hi hkm))
      rw [guard_succ,guard_succ,shift_and hprev.isUFormula (domainCode_isSemiformula (h.nth hkm)).isUFormula,
        ih env m n h (le_of_lt hkm),domainCode_targetShift (h.nth hkm),targetShiftTerms_nth h hkm]
  exact hall k env m n h hk
#print axioms targetShift_invariant
#print axioms guard_targetShift
end M6.PA.NumericPAeqValueDomainGuard

