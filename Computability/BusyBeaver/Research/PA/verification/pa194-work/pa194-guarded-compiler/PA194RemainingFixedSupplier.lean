import PA194GuardedClosed
import PA194ClosedSentenceEnvironment
import PA194ForwardFixedFour

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace PA194GuardedCompiler
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194SourceTemplates PA194PAeqOrdinalValues PA194TermDispatcher
open PA194FormulaDispatcher PA194Schematic PA194ForwardTyped PA194ForwardReflProof
open M6.PA.RelationalSource.Ordinal (Term)

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The compiler's translation and the quoted standard translation agree on closed formulas. -/
theorem tr_closed_quote (σ : SourceFormula 0) (hc : σ.freeVariables = ∅) :
    tr (⌜σ⌝ : V) =
      (⌜formula σ (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V) := by
  rw [← rootFormula_quote]
  change translateFormula (idParam ((⌜σ⌝ : V) + 1)) (⌜σ⌝ : V) =
    translateFormula (rootParameters (⌜σ⌝ : V)) (⌜σ⌝ : V)
  symm
  have hs : IsSemiformula PA194PAeq.language 0 (⌜σ⌝ : V) := by simp
  exact PA194ClosedEnvironment.sentence_root_packet hs.isUFormula
    (quote_shift_fixed' hc) (idParam_identity _).1

private theorem typed_univCl_eq (σ : SourceFormula 0) (hc : σ.freeVariables = ∅) :
    (Rewriting.emb σ.univCl : SourceFormula 0) = σ := by
  change (σ.univCl : Proposition PA194PAeq.language) = σ
  rw [Semiformula.coe_univCl_eq_univCl']
  exact Semiformula.univCl'_eq_self_of _ hc

variable {T : Theory SourceL} [T.Δ₁]

/-- Supply the four remaining fixed axioms of the interpretation from source naming and
arithmetic facts. The addition and multiplication recursion facts are explicit premises. -/
theorem remaining_fixed_supplier (S : SourceFacts (V := V) T)
    (hdom : Provable T (^∃ (domainCode (^#(0 : V)))))
    (hA3 : T.internalize V ⊢ tHyp sA3) (hM3 : T.internalize V ⊢ tHyp sM3)
    (σ : Sentence PA194PAeq.language) (hσ : σ ∈ remainingFixedAfterSuccCongruence) :
    Provable T (⌜formula (Rewriting.emb σ : SourceFormula 0)
      (Fin.elim0 : Fin 0 → Term 0) (fun _ : Nat => (.fvar 0 : Term 0))⌝ : V) := by
  change σ ∈ [PA194PAeq.addCongruence.univCl, PA194PAeq.mulCongruence.univCl,
    PA194PAeq.addSucc.univCl, PA194PAeq.mulSucc.univCl] at hσ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hσ
  rcases hσ with rfl | rfl | rfl | rfl
  · rw [typed_univCl_eq _ (by decide), ← tr_closed_quote _ (by decide)]
    exact addCongruence_provable S hdom
  · rw [typed_univCl_eq _ (by decide), ← tr_closed_quote _ (by decide)]
    exact mulCongruence_provable S hdom
  · rw [typed_univCl_eq _ (by decide), ← tr_closed_quote _ (by decide)]
    exact addSucc_provable S hdom hA3
  · rw [typed_univCl_eq _ (by decide), ← tr_closed_quote _ (by decide)]
    exact mulSucc_provable S hdom hM3

#print axioms tr_closed_quote
#print axioms remaining_fixed_supplier
end generic
end PA194GuardedCompiler
