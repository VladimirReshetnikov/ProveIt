module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqValueIsoGuardValidity
public import PA196.Arithmetic.Transport.FoundationRelationalSequentPropositional
public import PA196.Arithmetic.Transport.FoundationRelationalSequentFold
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqValueIsoGuard


/-! Actual native projection certificates by model-count induction. The
term environment remains explicit; no domain assumption is asserted true. -/
namespace PA196.Arithmetic.Transport.NumericPAeqValueIsoGuard
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric NumericPAeqTerm
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence PA196.Arithmetic.Checker
open RelationalSource (language)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] M6.PA.NumericPAeqValueIsoGuard.guardGraph translateGraph acceptedArrowGraph templateTwoGraph
noncomputable def projectionGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “code param env other k i. ∃ g t u d a b,
    !M6.PA.NumericPAeqValueIsoGuard.guardGraph g env other k ∧ !nthDef t env i ∧ !nthDef u other i ∧ !isoCodeGraph d t u ∧
    !translateGraph a param g ∧ !translateGraph b param d ∧ !acceptedArrowGraph code a b”
theorem projection_graph (code param env other k i : V) :
    projectionGraph.val.Evalb ![code,param,env,other,k,i] ↔
      verifyValue code=wim (translate param (M6.PA.NumericPAeqValueIsoGuard.guard env other k))
        (translate param (isoCode (nth env i) (nth other i)))+1 := by
  simp [projectionGraph,M6.PA.NumericPAeqValueIsoGuard.guard_graph,isoCode,translate_graph,acceptedArrow_graph,Matrix.comp_vecCons'']

attribute [local irreducible] projectionGraph
noncomputable def projectionInvariant : ArithmeticSemisentence 1 :=
  “k. ∀ param env other n i, i<k →
    (∀ j<k, ∃ t, !nthDef t env j ∧ !((isSemiterm language).sigma) n t ∧ ∃ u, !nthDef u other j ∧ !((isSemiterm language).sigma) n u) →
    ∃ code, !projectionGraph code param env other k i”
theorem projection_invariant (k : V) : projectionInvariant.Evalb ![k] ↔
    ∀ param env other n i : V, i<k →
      (∀ j<k, IsSemiterm language n (nth env j) ∧ IsSemiterm language n (nth other j)) →
      ∃ code, verifyValue code=wim (translate param (M6.PA.NumericPAeqValueIsoGuard.guard env other k))
        (translate param (isoCode (nth env i) (nth other i)))+1 := by
  simp [projectionInvariant,projection_graph,Matrix.comp_vecCons'']

attribute [local irreducible] projectionInvariant M6.PA.NumericPAeqValueIsoGuard.guard translate
variable [V↓[ℒₒᵣ] ⊧* theory]

theorem guard_projection_certificate (param env other k n i : V) (hi:i<k)
    (h:∀ j<k, IsSemiterm language n (nth env j) ∧ IsSemiterm language n (nth other j)) :
    ∃ code, verifyValue code=wim (translate param (M6.PA.NumericPAeqValueIsoGuard.guard env other k))
      (translate param (isoCode (nth env i) (nth other i)))+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ k : V, ∀ param env other n i : V, i<k →
      (∀ j<k, IsSemiterm language n (nth env j) ∧ IsSemiterm language n (nth other j)) →
      ∃ code, verifyValue code=wim (translate param (M6.PA.NumericPAeqValueIsoGuard.guard env other k))
        (translate param (isoCode (nth env i) (nth other i)))+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun k : V =>
      ∀ param env other n i : V, i<k →
        (∀ j<k, IsSemiterm language n (nth env j) ∧ IsSemiterm language n (nth other j)) →
        ∃ code, verifyValue code=wim (translate param (M6.PA.NumericPAeqValueIsoGuard.guard env other k))
          (translate param (isoCode (nth env i) (nth other i)))+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb projectionInvariant,by trivial,?_⟩
      intro k; simpa using (projection_invariant (V:=V) k).symm
    · intro param env other n i hi _; exact False.elim (not_lt_zero hi)
    · intro k ih param env other n i hi h
      have old : ∀ j<k, IsSemiterm language n (nth env j) ∧ IsSemiterm language n (nth other j) :=
        fun j hj => h j (lt_trans hj (lt_add_one k))
      have hg := (M6.PA.NumericPAeqValueIsoGuard.guard_isSemiformula env other k n old).isUFormula
      have hd := (isoCode_isSemiformula (h k (lt_add_one k)).1 (h k (lt_add_one k)).2).isUFormula
      rw [M6.PA.NumericPAeqValueIsoGuard.guard_succ,translate_and _ _ _ hg hd,translationAnd_eq]
      let a := translate param (M6.PA.NumericPAeqValueIsoGuard.guard env other k)
      let b := translate param (isoCode (nth env k) (nth other k))
      let assumption : Context [wa a b] (wa a b) := .assumption (by simp)
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hi) with he|hlt
      · subst i
        let out := assumption.andRight.deduction.empty
        exact ⟨out.code,out.accepted⟩
      · obtain ⟨code,hcode⟩ := ih param env other n i hlt old
        let left := assumption.andLeft.deduction.empty
        let out := implicationCompose left (⟨code,hcode⟩)
        exact ⟨out.code,out.accepted⟩
  exact hall k param env other n i hi h

#print axioms projection_graph
#print axioms projection_invariant
#print axioms guard_projection_certificate
end PA196.Arithmetic.Transport.NumericPAeqValueIsoGuard
