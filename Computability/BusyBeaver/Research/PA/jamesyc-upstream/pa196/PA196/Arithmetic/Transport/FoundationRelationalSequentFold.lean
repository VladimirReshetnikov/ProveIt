module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentMember
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Full-PA numeric fold elimination. Its premise is explicit accepted-code
existence for every actual HFS member, not an external proof compiler. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

attribute [local irreducible] ActualArithmeticGraph.graph translateGraph sequentScanGraph verifyGraph
noncomputable def acceptedArrowGraph : 𝚺ᴬ₁.Semisentence 3 := .mkSigma
  “code a b. ∃ ab, !(ActualArithmeticGraph.graph PA196.Arithmetic.HeadGraphs.implicationExpr) ab a b 0 0 ∧
    !verifyGraph (ab+1) code”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem acceptedArrow_graph (code a b : V) :
    acceptedArrowGraph.val.Evalb ![code,a,b] ↔ verifyValue code=wim a b+1 := by
  simp [acceptedArrowGraph,ActualArithmeticGraph.graph_correct,verify_graph,
    wim,implicationValue,Matrix.comp_vecCons'',eq_comm]

attribute [local irreducible] acceptedArrowGraph
noncomputable def foldScanInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ param s c,
    (∀ p, p∈s → ∃ a code, !translateGraph a param p ∧ !acceptedArrowGraph code a c) →
    ∃ out code, !sequentScanGraph out param s n ∧ !acceptedArrowGraph code out c”

theorem foldScan_invariant (n : V) : foldScanInvariant.Evalb ![n] ↔
    ∀ param s c : V,
      (∀ p, p∈s → ∃ code, verifyValue code=wim (translate param p) c+1) →
      ∃ code, verifyValue code=wim (sequentScan param s n) c+1 := by
  simp [foldScanInvariant,translate_graph,sequentScan_graph,acceptedArrow_graph,Matrix.comp_vecCons'']

attribute [local irreducible] sequentScan translate foldScanInvariant
variable [V↓[ℒₒᵣ] ⊧* theory]

theorem scan_eliminate_certificate (n param s c : V)
    (h : ∀ p, p∈s → ∃ code, verifyValue code=wim (translate param p) c+1) :
    ∃ code, verifyValue code=wim (sequentScan param s n) c+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ param s c : V,
      (∀ p, p∈s → ∃ code, verifyValue code=wim (translate param p) c+1) →
      ∃ code, verifyValue code=wim (sequentScan param s n) c+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ param s c : V,
        (∀ p, p∈s → ∃ code, verifyValue code=wim (translate param p) c+1) →
        ∃ code, verifyValue code=wim (sequentScan param s n) c+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb foldScanInvariant,by trivial,?_⟩
      intro n
      simpa using (foldScan_invariant (V:=V) n).symm
    · intro param s c h
      rw [sequentScan_zero]
      exact ⟨(explosion c).code,(explosion c).accepted⟩
    · intro n ih param s c h
      obtain ⟨code,hcode⟩ := ih param s c h
      by_cases hm : n∈s
      · obtain ⟨leaf,hleaf⟩ := h n hm
        rw [sequentScan_mem _ _ _ hm,translationOr_eq]
        let out := orEliminate (⟨leaf,hleaf⟩ : Certificate (wim (translate param n) c))
          (⟨code,hcode⟩ : Certificate (wim (sequentScan param s n) c))
        exact ⟨out.code,out.accepted⟩
      · rw [sequentScan_not_mem _ _ _ hm]
        exact ⟨code,hcode⟩
  exact hall n param s c h

theorem sequent_eliminate_certificate (param s c : V)
    (h : ∀ p, p∈s → ∃ code, verifyValue code=wim (translate param p) c+1) :
    ∃ code, verifyValue code=wim (sequentCode param s) c+1 :=
  scan_eliminate_certificate s param s c h

theorem sequent_weakening_certificate (param s t : V) (h : s⊆t) :
    ∃ code, verifyValue code=wim (sequentCode param s) (sequentCode param t)+1 := by
  apply sequent_eliminate_certificate
  intro p hp
  exact member_certificate param t p (h hp)

#print axioms acceptedArrow_graph
#print axioms foldScan_invariant
#print axioms scan_eliminate_certificate
#print axioms sequent_eliminate_certificate
#print axioms sequent_weakening_certificate
end PA196.Arithmetic.Transport.RelationalSource.Numeric

