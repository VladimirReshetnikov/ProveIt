import PA194InternalBitDiagonal
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalBitDiagonalTerm
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BitTranslation PA194ContradictionTranslation PA194ContradictionInternalRefutation PA194InternalBitDiagonal
open DiophantineConsistency
section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma typed_body_subst_term (t : Bootstrapping.Term V ℒₒᵣ) :
    Bootstrapping.Semiformula.subst ![t] (⌜contradictionBody⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) =
      ∼(Bootstrapping.Semiformula.subst ![t,t]
        (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2)) := by
  rw [body_eq]
  simp [Semiformula.typed_quote_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail]

lemma internal_PA_proves_bit_diag_neg_term (t : Bootstrapping.Term V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∼(Bootstrapping.Semiformula.subst ![t,t]
        (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2)) := by
  let b := PA_proves_not_contradiction.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜(∼contradiction).univCl⌝ : V) :=
    ⟨⌜b⌝, proof_of_quote_proof b⟩
  rw [quote_univ_contradiction] at hb
  let body : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⌜contradictionBody⌝
  have ht : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (∀⁰ body) := (tprovable_iff_provable).mpr hb
  have hs := TProof.specialize! ht t
  simpa [body,typed_body_subst_term] using hs
#print axioms internal_PA_proves_bit_diag_neg_term
end model
end PA194InternalBitDiagonalTerm
