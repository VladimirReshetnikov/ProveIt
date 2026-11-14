import PA194ContradictionInternalRefutation
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194InternalSingleton
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency

@[irreducible] def singletonCore : ArithmeticSemisentence 3 :=
  ((bitDef.val ⇜ ![#0,#1]) 🡘 op(=).operator ![#0,#2])

def singletonSentence : ArithmeticSentence := ∀⁰ ∃⁰ ∀⁰ singletonCore

theorem ISigma1_proves_singleton : (𝗜𝚺₁ : ArithmeticTheory) ⊢ singletonSentence := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, singletonSentence, Semiformula.eval_all, Semiformula.eval_ex]
  intro a
  refine ⟨({a} : M), ?_⟩
  intro x
  simp only [singletonCore, LogicalConnective.HomClass.map_iff]
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val ![x,({a}:M),a] Empty.elim ∘ (Rew.subst ![#0,#1] : Rew ℒₒᵣ Empty 2 Empty 3) ∘ Semiterm.bvar) = ![x,({a}:M)] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hf : (Semiterm.val ![x,({a}:M),a] Empty.elim ∘ (Rew.subst ![#0,#1] : Rew ℒₒᵣ Empty 2 Empty 3) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  have hbit : bitDef.val.Evalb ![x,({a}:M)] ↔ x ∈ ({a}:M) := by
    simpa using bit_defined.defined ![x,({a}:M)]
  simpa [Semiformula.Evalb] using hbit.trans (mem_singleton_iff (i := x) (j := a))
theorem PA_proves_singleton : (𝗣𝗔 : ArithmeticTheory) ⊢ singletonSentence :=
  Entailment.WeakerThan.pbl ISigma1_proves_singleton

section model
open LO.FirstOrder.Arithmetic.Bootstrapping
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma internal_PA_singleton (a : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (⌜(∃⁰ ∀⁰ singletonCore : ArithmeticSemisentence 1)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst
        ![Bootstrapping.Semiterm.fvar a] := by
  let b := PA_proves_singleton.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜singletonSentence⌝ : V) := ⟨⌜b⌝, proof_of_quote_proof b⟩
  have he : (⌜singletonSentence⌝ : V) = ^∀ (⌜(∃⁰ ∀⁰ singletonCore : ArithmeticSemisentence 1)⌝ : V) := by
    rw [Sentence.quote_def, singletonSentence, Rewriting.app_all, Rew.q_emb, Semiformula.quote_all, ← Sentence.quote_def]
  have ht : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∀⁰ (⌜(∃⁰ ∀⁰ singletonCore : ArithmeticSemisentence 1)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) := by
    apply (tprovable_iff_provable).mpr
    rw [he] at hb
    exact hb
  exact TProof.specialize! ht (Bootstrapping.Semiterm.fvar a)

lemma singleton_subst_shape (a : V) :
    (⌜(∃⁰ ∀⁰ singletonCore : ArithmeticSemisentence 1)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1).subst
        ![Bootstrapping.Semiterm.fvar a] =
      ∃⁰ ∀⁰ (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1]) 🡘
        ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar a)) := by
  have hemb : (Rewriting.emb (bitDef.val ⇜ ![#0,#1]) : ArithmeticSemiformula Nat 3) =
      (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) ⇜ ![#0,#1] := by
    rw [Semiformula.coe_subst_eq_subst_coe]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  simp [Sentence.typed_quote_def, singletonCore, hemb, Semiformula.typed_quote_substs,
    Bootstrapping.Semiformula.substs_substs, SemitermVec.q, Matrix.vecHead, Matrix.vecTail]

lemma internal_PA_singleton_explicit (a : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∃⁰ ∀⁰ (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1]) 🡘
        ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar a)) := by
  rw [← singleton_subst_shape]
  exact internal_PA_singleton a

#print axioms internal_PA_singleton_explicit
#print axioms singleton_subst_shape
#print axioms internal_PA_singleton
end model
#print axioms ISigma1_proves_singleton
end PA194InternalSingleton
