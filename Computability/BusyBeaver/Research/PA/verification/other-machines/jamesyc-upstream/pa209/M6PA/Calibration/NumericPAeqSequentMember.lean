module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentSupported
@[expose] public section

/-! Member injection by displayed full-PA model-length induction. All witnesses
are accepted numeric certificates, including for nonstandard HFS sequents. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric (translate translateGraph translate_graph translate_or translationOr_eq orLeft orRight)
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

attribute [local irreducible] formulaSyntaxGraph translateGraph sequentScanGraph RelationalSource.Numeric.acceptedArrowGraph
noncomputable def scanArrowGraph : 𝚺ᴬ₁.Semisentence 6 := .mkSigma
  “code native param s n p. ∃ source folded a b,
    !formulaSyntaxGraph source param p ∧ !sequentScanGraph folded param s n ∧
    !translateGraph a native source ∧ !translateGraph b native folded ∧
    !RelationalSource.Numeric.acceptedArrowGraph code a b”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem scanArrow_graph (code native param s n p : V) :
    scanArrowGraph.val.Evalb ![code,native,param,s,n,p] ↔
      verifyValue code = wim (translate native (formulaSyntax param p))
        (translate native (sequentScan param s n))+1 := by
  simp [scanArrowGraph,formulaSyntax_graph,sequentScan_graph,translate_graph,
    RelationalSource.Numeric.acceptedArrow_graph,Matrix.comp_vecCons'']

attribute [local irreducible] scanArrowGraph supportedSetGraph
noncomputable def memberScanInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ native param s p, !supportedSetGraph param s → p∈s → p<n → ∃ code, !scanArrowGraph code native param s n p”

theorem memberScan_invariant (n : V) : memberScanInvariant.Evalb ![n] ↔
    ∀ native param s p : V, SupportedSet param s → p∈s → p<n → ∃ code,
      verifyValue code = wim (translate native (formulaSyntax param p)) (translate native (sequentScan param s n))+1 := by
  simp [memberScanInvariant,scanArrow_graph,supportedSet_graph,Matrix.comp_vecCons'']

attribute [local irreducible] sequentScan translate memberScanInvariant

theorem scan_member_certificate (n native param s p : V) (hs : SupportedSet param s) (hm : p∈s) (hn : p<n) :
    ∃ code, verifyValue code = wim (translate native (formulaSyntax param p)) (translate native (sequentScan param s n))+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ native param s p : V, SupportedSet param s → p∈s → p<n → ∃ code,
      verifyValue code = wim (translate native (formulaSyntax param p)) (translate native (sequentScan param s n))+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ native param s p : V, SupportedSet param s → p∈s → p<n → ∃ code,
        verifyValue code = wim (translate native (formulaSyntax param p)) (translate native (sequentScan param s n))+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb memberScanInvariant,by trivial,?_⟩
      intro n
      simpa using (memberScan_invariant (V:=V) n).symm
    · intro native param s p hs hm hp
      exact False.elim (not_lt_zero hp)
    · intro n ih native param s p hs hm hp
      rcases eq_or_lt_of_le (lt_succ_iff_le.mp hp) with he | hlt
      · subst p
        rw [sequentScan_mem _ _ _ hm,translate_or _ _ _ (hs.member_valid hm) (hs.scan_valid n),translationOr_eq]
        exact ⟨(orLeft (translate native (formulaSyntax param n)) (translate native (sequentScan param s n))).code,
          (orLeft (translate native (formulaSyntax param n)) (translate native (sequentScan param s n))).accepted⟩
      · obtain ⟨code,hcode⟩ := ih native param s p hs hm hlt
        by_cases hns : n∈s
        · rw [sequentScan_mem _ _ _ hns,translate_or _ _ _ (hs.member_valid hns) (hs.scan_valid n),translationOr_eq]
          let out := implicationCompose (⟨code,hcode⟩ : Certificate
            (wim (translate native (formulaSyntax param p)) (translate native (sequentScan param s n))))
            (orRight (translate native (formulaSyntax param n)) (translate native (sequentScan param s n)))
          exact ⟨out.code,out.accepted⟩
        · rw [sequentScan_not_mem _ _ _ hns]
          exact ⟨code,hcode⟩
  exact hall n native param s p hs hm hn

theorem member_certificate (native param s p : V) (hs : SupportedSet param s) (hm : p∈s) :
    ∃ code, verifyValue code = wim (translate native (formulaSyntax param p)) (translate native (sequentCode param s))+1 :=
  scan_member_certificate s native param s p hs hm (lt_of_mem hm)

#print axioms scanArrow_graph
#print axioms memberScan_invariant
#print axioms scan_member_certificate
#print axioms member_certificate
end M6.PA.NumericPAeqFormula.Sequent

