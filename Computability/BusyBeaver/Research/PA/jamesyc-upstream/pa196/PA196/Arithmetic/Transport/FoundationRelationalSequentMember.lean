module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentLogic
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Member injection by displayed full-PA model-length induction. All witnesses
are accepted numeric certificates, including for nonstandard HFS sequents. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

attribute [local irreducible] ActualArithmeticGraph.graph translateGraph sequentScanGraph verifyGraph
noncomputable def scanArrowGraph : 𝚺ᴬ₁.Semisentence 5 := .mkSigma
  “code param s n p. ∃ a b ab, !translateGraph a param p ∧
    !sequentScanGraph b param s n ∧
    !(ActualArithmeticGraph.graph PA196.Arithmetic.HeadGraphs.implicationExpr) ab a b 0 0 ∧
    !verifyGraph (ab+1) code”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem scanArrow_graph (code param s n p : V) :
    scanArrowGraph.val.Evalb ![code,param,s,n,p] ↔
      verifyValue code = wim (translate param p) (sequentScan param s n)+1 := by
  simp [scanArrowGraph,translate_graph,sequentScan_graph,ActualArithmeticGraph.graph_correct,
    verify_graph,wim,implicationValue,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] scanArrowGraph
noncomputable def memberScanInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ param s p, p∈s → p<n → ∃ code, !scanArrowGraph code param s n p”

theorem memberScan_invariant (n : V) : memberScanInvariant.Evalb ![n] ↔
    ∀ param s p : V, p∈s → p<n → ∃ code,
      verifyValue code = wim (translate param p) (sequentScan param s n)+1 := by
  simp [memberScanInvariant,scanArrow_graph,Matrix.comp_vecCons'']

attribute [local irreducible] sequentScan translate memberScanInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]

theorem scan_member_certificate (n param s p : V) (hm : p∈s) (hn : p<n) :
    ∃ code, verifyValue code = wim (translate param p) (sequentScan param s n)+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ param s p : V, p∈s → p<n → ∃ code,
      verifyValue code = wim (translate param p) (sequentScan param s n)+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ param s p : V, p∈s → p<n → ∃ code,
        verifyValue code = wim (translate param p) (sequentScan param s n)+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb memberScanInvariant,by trivial,?_⟩
      intro n
      simpa using (memberScan_invariant (V:=V) n).symm
    · intro param s p hm hp
      exact False.elim (not_lt_zero hp)
    · intro n ih param s p hm hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        rw [sequentScan_mem _ _ _ hm,translationOr_eq]
        exact ⟨(orLeft (translate param n) (sequentScan param s n)).code,
          (orLeft (translate param n) (sequentScan param s n)).accepted⟩
      · obtain ⟨code,hcode⟩ := ih param s p hm hlt
        by_cases hns : n∈s
        · rw [sequentScan_mem _ _ _ hns,translationOr_eq]
          let out := implicationCompose (⟨code,hcode⟩ : Certificate
            (wim (translate param p) (sequentScan param s n)))
            (orRight (translate param n) (sequentScan param s n))
          exact ⟨out.code,out.accepted⟩
        · rw [sequentScan_not_mem _ _ _ hns]
          exact ⟨code,hcode⟩
  exact hall n param s p hm hn

theorem member_certificate (param s p : V) (hm : p∈s) :
    ∃ code, verifyValue code = wim (translate param p) (sequentCode param s)+1 :=
  scan_member_certificate s param s p hm (lt_of_mem hm)

#print axioms scanArrow_graph
#print axioms memberScan_invariant
#print axioms scan_member_certificate
#print axioms member_certificate
end PA196.Arithmetic.Transport.RelationalSource.Numeric

