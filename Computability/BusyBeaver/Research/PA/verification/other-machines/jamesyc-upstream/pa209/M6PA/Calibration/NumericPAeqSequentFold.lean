module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentMember
@[expose] public section

/-! Full-PA numeric fold elimination. Its premise is explicit accepted-code
existence for every actual HFS member, not an external proof compiler. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric (translate translateGraph translate_graph translate_or translate_falsum translationOr_eq orEliminate acceptedArrowGraph acceptedArrow_graph)
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

attribute [local irreducible] formulaSyntaxGraph translateGraph sequentScanGraph supportedSetGraph
attribute [local irreducible] acceptedArrowGraph
noncomputable def foldScanInvariant : ArithmeticSemisentence 1 :=
  “n. ∀ native param s c, !supportedSetGraph param s →
    (∀ p, p∈s → ∃ source a code, !formulaSyntaxGraph source param p ∧ !translateGraph a native source ∧ !acceptedArrowGraph code a c) →
    ∃ source out code, !sequentScanGraph source param s n ∧ !translateGraph out native source ∧ !acceptedArrowGraph code out c”

theorem foldScan_invariant (n : V) : foldScanInvariant.Evalb ![n] ↔
    ∀ native param s c : V, SupportedSet param s →
      (∀ p, p∈s → ∃ code, verifyValue code=wim (translate native (formulaSyntax param p)) c+1) →
      ∃ code, verifyValue code=wim (translate native (sequentScan param s n)) c+1 := by
  simp [foldScanInvariant,supportedSet_graph,formulaSyntax_graph,translate_graph,sequentScan_graph,acceptedArrow_graph,Matrix.comp_vecCons'']

attribute [local irreducible] sequentScan translate foldScanInvariant

theorem scan_eliminate_certificate (n native param s c : V) (hs : SupportedSet param s)
    (h : ∀ p, p∈s → ∃ code, verifyValue code=wim (translate native (formulaSyntax param p)) c+1) :
    ∃ code, verifyValue code=wim (translate native (sequentScan param s n)) c+1 := by
  let : InductionScheme ℒₒᵣ Set.univ ⪯ theory :=
    Entailment.WeakerThan.ofSubset Set.subset_union_right
  have : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ Set.univ :=
    models_of_subtheory (inferInstance : V↓[ℒₒᵣ] ⊧* theory)
  have hall : ∀ n : V, ∀ native param s c : V, SupportedSet param s →
      (∀ p, p∈s → ∃ code, verifyValue code=wim (translate native (formulaSyntax param p)) c+1) →
      ∃ code, verifyValue code=wim (translate native (sequentScan param s n)) c+1 := by
    refine InductionScheme.succ_induction (C:=Set.univ) (P:=fun n : V =>
      ∀ native param s c : V, SupportedSet param s →
        (∀ p, p∈s → ∃ code, verifyValue code=wim (translate native (formulaSyntax param p)) c+1) →
        ∃ code, verifyValue code=wim (translate native (sequentScan param s n)) c+1) ?_ ?_ ?_
    · refine ⟨fun _ => 0,Rewriting.emb foldScanInvariant,by trivial,?_⟩
      intro n
      simpa using (foldScan_invariant (V:=V) n).symm
    · intro native param s c hs h
      rw [sequentScan_zero,translate_falsum]
      exact ⟨(explosion c).code,(explosion c).accepted⟩
    · intro n ih native param s c hs h
      obtain ⟨code,hcode⟩ := ih native param s c hs h
      by_cases hm : n∈s
      · obtain ⟨leaf,hleaf⟩ := h n hm
        rw [sequentScan_mem _ _ _ hm,translate_or _ _ _ (hs.member_valid hm) (hs.scan_valid n),translationOr_eq]
        let out := orEliminate (⟨leaf,hleaf⟩ : Certificate (wim (translate native (formulaSyntax param n)) c))
          (⟨code,hcode⟩ : Certificate (wim (translate native (sequentScan param s n)) c))
        exact ⟨out.code,out.accepted⟩
      · rw [sequentScan_not_mem _ _ _ hm]
        exact ⟨code,hcode⟩
  exact hall n native param s c hs h

theorem sequent_eliminate_certificate (native param s c : V) (hs : SupportedSet param s)
    (h : ∀ p, p∈s → ∃ code, verifyValue code=wim (translate native (formulaSyntax param p)) c+1) :
    ∃ code, verifyValue code=wim (translate native (sequentCode param s)) c+1 :=
  scan_eliminate_certificate s native param s c hs h

theorem sequent_weakening_certificate (native param s t : V) (hs : SupportedSet param s) (ht : SupportedSet param t) (h : s⊆t) :
    ∃ code, verifyValue code=wim (translate native (sequentCode param s)) (translate native (sequentCode param t))+1 := by
  apply sequent_eliminate_certificate native param s _ hs
  intro p hp
  exact member_certificate native param t p ht (h hp)

#print axioms foldScan_invariant
#print axioms scan_eliminate_certificate
#print axioms sequent_eliminate_certificate
#print axioms sequent_weakening_certificate
end M6.PA.NumericPAeqFormula.Sequent

