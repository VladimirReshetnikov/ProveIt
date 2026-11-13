module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqValueDomainGuardProjection
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueDomainGuard

namespace PA196.Arithmetic.Transport.NumericPAeqValueDomainGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
attribute [local irreducible] M6.PA.NumericPAeqValueDomainGuard.guardGraph translateGraph acceptedArrowGraph
noncomputable def collectionGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “code assumption param env k. ∃ g out, !M6.PA.NumericPAeqValueDomainGuard.guardGraph g env k ∧
    !translateGraph out param g ∧ !acceptedArrowGraph code assumption out”
theorem collection_graph (code assumption param env k:V):
    collectionGraph.val.Evalb ![code,assumption,param,env,k] ↔
      verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k))+1 := by
  simp [collectionGraph,M6.PA.NumericPAeqValueDomainGuard.guard_graph,translate_graph,acceptedArrow_graph,Matrix.comp_vecCons'']
attribute [local irreducible] collectionGraph
noncomputable def collectionInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ assumption param env n,
    (∀ i<k, ∃ x, !nthDef x env i ∧ !((isSemiterm language).sigma) n x) →
    (∀ i<k, ∃ x e out code, !nthDef x env i ∧ !NumericPAeqTerm.domainCodeGraph e x ∧ !translateGraph out param e ∧
      !acceptedArrowGraph code assumption out) →
    ∃ code, !collectionGraph code assumption param env k”
theorem collection_invariant (k:V):collectionInvariant.Evalb ![k] ↔
    ∀assumption param env n:V,
      (∀i<k,IsSemiterm language n (nth env i)) →
      (∀i<k,∃code,verifyValue code=wim assumption (translate param (NumericPAeqTerm.domainCode (nth env i)))+1) →
      ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k))+1 := by
  simp [collectionInvariant,NumericPAeqTerm.domainCode_graph,NumericPAeqTerm.domainCode,translate_graph,acceptedArrow_graph,collection_graph,Matrix.comp_vecCons'']
attribute [local irreducible] collectionInvariant M6.PA.NumericPAeqValueDomainGuard.guard translate
theorem guard_collection_certificate (assumption param env k n:V)
    (h:∀i<k,IsSemiterm language n (nth env i))
    (hs:∀i<k,∃code,verifyValue code=wim assumption (translate param (NumericPAeqTerm.domainCode (nth env i)))+1):
    ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k))+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory := Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ := models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀k:V,∀assumption param env n:V,
      (∀i<k,IsSemiterm language n (nth env i)) →
      (∀i<k,∃code,verifyValue code=wim assumption (translate param (NumericPAeqTerm.domainCode (nth env i)))+1) →
      ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k))+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k:V=>∀assumption param env n:V,
      (∀i<k,IsSemiterm language n (nth env i)) →
      (∀i<k,∃code,verifyValue code=wim assumption (translate param (NumericPAeqTerm.domainCode (nth env i)))+1) →
      ∃code,verifyValue code=wim assumption (translate param (M6.PA.NumericPAeqValueDomainGuard.guard env k))+1) ?_ ?_ ?_
    · refine ⟨fun _=>0,Rewriting.emb collectionInvariant,by trivial,?_⟩
      intro k; simpa using (collection_invariant (V:=V) k).symm
    · intro assumption param env n _ _
      rw [M6.PA.NumericPAeqValueDomainGuard.guard_zero,translate_verum]
      let p : Context [assumption] 0 := .closed truthCertificate
      exact ⟨p.deduction.empty.code,p.deduction.empty.accepted⟩
    · intro k ih assumption param env n h hs
      have old : ∀i<k,IsSemiterm language n (nth env i) :=
        fun i hi=>h i (lt_trans hi (lt_add_one k))
      obtain ⟨left,hl⟩ := ih assumption param env n old (fun i hi=>hs i (lt_trans hi (lt_add_one k)))
      obtain ⟨right,hr⟩ := hs k (lt_add_one k)
      rw [M6.PA.NumericPAeqValueDomainGuard.guard_succ,translate_and _ _ _ (M6.PA.NumericPAeqValueDomainGuard.guard_isSemiformula env k n old).isUFormula
        (NumericPAeqTerm.domainCode_isSemiformula (h k (lt_add_one k))).isUFormula,translationAnd_eq]
      let base : Context [assumption] assumption := .assumption (by simp)
      let lp := base.mp (.closed (⟨left,hl⟩ : Certificate _))
      let rp := base.mp (.closed (⟨right,hr⟩ : Certificate _))
      let out := (lp.andIntro rp).deduction.empty
      exact ⟨out.code,out.accepted⟩
  exact hall k assumption param env n h hs
#print axioms collection_graph
#print axioms collection_invariant
#print axioms guard_collection_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueDomainGuard

