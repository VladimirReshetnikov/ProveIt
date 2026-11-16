module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueRealizationGuardProjection
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueRealizationGuard

namespace PA196.Arithmetic.Transport.NumericPAeqValueRealizationGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] M6.PA.NumericPAeqValueRealizationGuard.guardGraph M6.PA.NumericPAeqValueRealizationGuard.entryGraph translateGraph acceptedArrowGraph
noncomputable def collectionGraph : 𝚺ᴬ₁.Semisentence 8 := .mkSigma
  “code assumption param b f w a k. ∃ g out, !M6.PA.NumericPAeqValueRealizationGuard.guardGraph g b f w a k ∧
    !translateGraph out param g ∧ !acceptedArrowGraph code assumption out”
theorem collection_graph (code assumption param b f w a k:V):
    collectionGraph.val.Evalb ![code,assumption,param,b,f,w,a,k] ↔
      verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.guard b f w a k))+1 := by
  simp [collectionGraph,M6.PA.NumericPAeqValueRealizationGuard.guard_graph,translate_graph,acceptedArrow_graph,Matrix.comp_vecCons'']
attribute [local irreducible] collectionGraph
noncomputable def collectionInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ assumption param b f w a n,
    (∀ i<k, ∃ e, !M6.PA.NumericPAeqValueRealizationGuard.entryGraph e b f w a i ∧ !((isSemiformula language).sigma) n e) →
    (∀ i<k, ∃ e out code, !M6.PA.NumericPAeqValueRealizationGuard.entryGraph e b f w a i ∧ !translateGraph out param e ∧
      !acceptedArrowGraph code assumption out) →
    ∃ code, !collectionGraph code assumption param b f w a k”
theorem collection_invariant (k:V):collectionInvariant.Evalb ![k] ↔
    ∀assumption param b f w a n:V,
      (∀i<k,IsSemiformula language n (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i)) →
      (∀i<k,∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i))+1) →
      ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.guard b f w a k))+1 := by
  simp [collectionInvariant,M6.PA.NumericPAeqValueRealizationGuard.entry_graph,translate_graph,acceptedArrow_graph,collection_graph,Matrix.comp_vecCons'']
attribute [local irreducible] collectionInvariant M6.PA.NumericPAeqValueRealizationGuard.guard translate
theorem guard_collection_certificate (assumption param b f w a k n:V)
    (h:∀i<k,IsSemiformula language n (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i))
    (hs:∀i<k,∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i))+1):
    ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.guard b f w a k))+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀assumption param b f w a n:V,
      (∀i<k,IsSemiformula language n (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i)) →
      (∀i<k,∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i))+1) →
      ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.guard b f w a k))+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀assumption param b f w a n:V,
      (∀i<k,IsSemiformula language n (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i)) →
      (∀i<k,∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i))+1) →
      ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueRealizationGuard.guard b f w a k))+1) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb collectionInvariant,by trivial,?_⟩
      intro k; simpa using (collection_invariant (V:=V) k).symm
    · intro assumption param b f w a n _ _
      rw [M6.PA.NumericPAeqValueRealizationGuard.guard_zero,translate_verum]
      let p : Context [assumption] 0 := .closed truthCertificate
      exact ⟨p.deduction.empty.code,p.deduction.empty.accepted⟩
    · intro k ih assumption param b f w a n h hs
      have old : ∀i<k,IsSemiformula language n (M6.PA.NumericPAeqValueRealizationGuard.entry b f w a i) :=
        fun i hi=>h i (lt_trans hi (lt_add_one k))
      obtain ⟨left,hl⟩ := ih assumption param b f w a n old (fun i hi=>hs i (lt_trans hi (lt_add_one k)))
      obtain ⟨right,hr⟩ := hs k (lt_add_one k)
      rw [M6.PA.NumericPAeqValueRealizationGuard.guard_succ,translate_and _ _ _ (M6.PA.NumericPAeqValueRealizationGuard.guard_isSemiformula b f w a k n old).isUFormula
        (h k (lt_add_one k)).isUFormula,translationAnd_eq]
      let base : Context [assumption] assumption := .assumption (by simp)
      let lp := base.mp (.closed (⟨left,hl⟩ : Certificate _))
      let rp := base.mp (.closed (⟨right,hr⟩ : Certificate _))
      let out := (lp.andIntro rp).deduction.empty
      exact ⟨out.code,out.accepted⟩
  exact hall k assumption param b f w a n h hs
#print axioms collection_graph
#print axioms collection_invariant
#print axioms guard_collection_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueRealizationGuard

