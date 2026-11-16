import PA194ContradictionInternalRefutation
import PA194DualAtomCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194InternalBitDiagonal
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BitTranslation PA194ContradictionTranslation PA194ContradictionInternalRefutation
open DiophantineConsistency

lemma body_eq : contradictionBody = ∼((Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2) ⇜ (![#0,#0] : Fin 2 → ArithmeticSemiterm Nat 1)) := by
  unfold contradictionBody contradiction bitTranslation substituteTwo
  rw [bitMatrix_eq]
  simp only [LogicalConnective.HomClass.map_neg, Rewriting.subst]
  rw [← TransitiveRewriting.comp_app, ← TransitiveRewriting.comp_app]
  congr 1
  congr 1
  congr 1
  apply Rew.ext
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Rew.comp_app,Rew.fixitr,Rew.fix]
    · exact Fin.cases (by simp [Rew.comp_app,Rew.fixitr,Rew.fix]) (fun j => Fin.elim0 j) j
  · intro x; exact Empty.elim x

section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma typed_body_subst (a : V) :
    Bootstrapping.Semiformula.subst (![Bootstrapping.Semiterm.fvar a] : Fin 1 → Bootstrapping.Term V ℒₒᵣ)
        (⌜contradictionBody⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) =
      ∼(Bootstrapping.Semiformula.subst ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar a]
        (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2)) := by
  rw [body_eq]
  simp [Semiformula.typed_quote_substs, Bootstrapping.Semiformula.substs_substs, Matrix.vecHead, Matrix.vecTail]

lemma internal_PA_proves_bit_diag_neg (a : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∼(Bootstrapping.Semiformula.subst ![Bootstrapping.Semiterm.fvar a,Bootstrapping.Semiterm.fvar a]
        (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2)) := by
  let b := PA_proves_not_contradiction.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜(∼contradiction).univCl⌝ : V) :=
    ⟨⌜b⌝, proof_of_quote_proof b⟩
  rw [quote_univ_contradiction] at hb
  let body : Bootstrapping.Semiformula V ℒₒᵣ 1 := ⌜contradictionBody⌝
  have ht : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (∀⁰ body) := by
    apply (tprovable_iff_provable).mpr
    exact hb
  have hs := TProof.specialize! ht (Bootstrapping.Semiterm.fvar a)
  simpa [body, typed_body_subst] using hs

#print axioms internal_PA_proves_bit_diag_neg
#print axioms typed_body_subst
end model
#print axioms body_eq
end PA194InternalBitDiagonal
