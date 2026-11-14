import PA194ContradictionTranslation
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Coding
/-! Lift the standard PA refutation of the distinguished contradiction into
arbitrary IΣ₁ models, then derive internal PA falsum from its provability. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194ContradictionInternalRefutation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ContradictionTranslation PA194BitTranslation

lemma neg_contradiction_fvSup : (∼contradiction).fvSup = 1 := by
  unfold contradiction bitTranslation substituteTwo bitMatrix
  decide

noncomputable def contradictionBody : ArithmeticSemiformula Nat 1 :=
  Rew.fixitr 0 1 ▹ (∼contradiction)

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma quote_univ_contradiction :
    (⌜(∼contradiction).univCl⌝ : V) = ^∀ (⌜contradictionBody⌝ : V) := by
  rw [quote_univCl_eq, neg_contradiction_fvSup]
  simp only [Nat.reduceAdd, Nat.cast_one]
  rw [show (1 : V) = 0+1 by simp, qqAlls_succ, qqAlls_zero]
  rfl

lemma quote_body_subst :
    (Bootstrapping.Semiformula.subst (![Bootstrapping.Semiterm.fvar (0 : V)] : Fin 1 → Bootstrapping.Term V ℒₒᵣ)
      (⌜contradictionBody⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1)).val = (⌜∼contradiction⌝ : V) := by
  have h := quote_subst_fvar_fixitr (V := V) (∼contradiction)
  rw [neg_contradiction_fvSup] at h
  change (⌜contradictionBody ⇜ (fun i : Fin 1 => (&↑i : SyntacticTerm ℒₒᵣ))⌝ : V) = _ at h
  change (⌜contradictionBody ⇜ (fun i : Fin 1 => (&↑i : SyntacticTerm ℒₒᵣ))⌝ : Bootstrapping.Formula V ℒₒᵣ).val = _ at h
  rw [Semiformula.typed_quote_substs] at h
  have hv : (fun i : Fin 1 => (⌜(&↑i : SyntacticTerm ℒₒᵣ)⌝ : Bootstrapping.Term V ℒₒᵣ)) = ![Bootstrapping.Semiterm.fvar 0] := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp
  simpa [hv] using h

lemma internal_PA_proves_neg_contradiction :
    Provable (𝗣𝗔 : ArithmeticTheory) (⌜∼contradiction⌝ : V) := by
  let b := PA_proves_not_contradiction.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜(∼contradiction).univCl⌝ : V) :=
    ⟨⌜b⌝, proof_of_quote_proof b⟩
  rw [quote_univ_contradiction] at hb
  let body : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⌜contradictionBody⌝
  have ht : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (∀⁰ body) := by
    apply (tprovable_iff_provable).mpr
    exact hb
  have hs := TProof.specialize! ht (Bootstrapping.Semiterm.fvar (0 : V))
  have hs' := (tprovable_iff_provable).mp hs
  change Provable (𝗣𝗔 : ArithmeticTheory)
    (Bootstrapping.Semiformula.subst (![Bootstrapping.Semiterm.fvar (0 : V)] : Fin 1 → Bootstrapping.Term V ℒₒᵣ) body).val at hs'
  rwa [quote_body_subst] at hs'

lemma contradiction_provable_implies_falsum
    (hp : Provable (𝗣𝗔 : ArithmeticTheory) (⌜contradiction⌝ : V)) :
    Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : V) := by
  have hn : Provable (𝗣𝗔 : ArithmeticTheory) (neg ℒₒᵣ (⌜contradiction⌝ : V)) := by
    have he : neg ℒₒᵣ (⌜contradiction⌝ : V) = (⌜∼contradiction⌝ : V) := by
      change (∼(⌜contradiction⌝ : Bootstrapping.Formula V ℒₒᵣ)).val =
        (⌜∼contradiction⌝ : Bootstrapping.Formula V ℒₒᵣ).val
      simp
    rw [he]
    exact internal_PA_proves_neg_contradiction
  have hempty : Derivable (𝗣𝗔 : ArithmeticTheory) (∅ : V) :=
    Derivable.cut (⌜contradiction⌝ : V) hp.toDerivable hn.toDerivable
  exact (Derivable.wk (s := insert (^⊥ : V) ∅) (by simp) (by simp) hempty).toProvable

#print axioms contradiction_provable_implies_falsum
#print axioms internal_PA_proves_neg_contradiction
#print axioms quote_body_subst
end model
#print axioms quote_univ_contradiction
#print axioms neg_contradiction_fvSup
end PA194ContradictionInternalRefutation
