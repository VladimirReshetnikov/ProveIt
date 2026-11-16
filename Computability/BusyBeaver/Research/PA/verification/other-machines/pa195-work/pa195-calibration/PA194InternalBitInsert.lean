import PA194InternalSingleton
set_option autoImplicit false
set_option maxHeartbeats 3000000
/-! A fixed standard IΣ₁ proof of bit-set insertion, quoted and specialized
    inside every IΣ₁ arithmetic model, including nonstandard parameters. -/
namespace PA194InternalBitInsert
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
@[irreducible] def insertCore : ArithmeticSemisentence 4 :=
  ((bitDef.val ⇜ ![#0,#1]) 🡘 ((bitDef.val ⇜ ![#0,#3]) ⋎ op(=).operator ![#0,#2]))
def insertSentence : ArithmeticSentence := ∀⁰ ∀⁰ ∃⁰ ∀⁰ insertCore

theorem ISigma1_proves_insert : (𝗜𝚺₁ : ArithmeticTheory) ⊢ insertSentence := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, insertSentence, Semiformula.eval_all, Semiformula.eval_ex]
  intro a b
  refine ⟨insert b a, ?_⟩
  intro x
  simp only [insertCore, LogicalConnective.HomClass.map_iff,LogicalConnective.HomClass.map_or]
  rw [Semiformula.eval_rew,Semiformula.eval_rew]
  have hv1 : (Semiterm.val ![x,insert b a,b,a] Empty.elim ∘ (Rew.subst ![#0,#1] : Rew ℒₒᵣ Empty 2 Empty 4) ∘ Semiterm.bvar) = ![x,insert b a] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hv2 : (Semiterm.val ![x,insert b a,b,a] Empty.elim ∘ (Rew.subst ![#0,#3] : Rew ℒₒᵣ Empty 2 Empty 4) ∘ Semiterm.bvar) = ![x,a] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hf1 : (Semiterm.val ![x,insert b a,b,a] Empty.elim ∘ (Rew.subst ![#0,#1] : Rew ℒₒᵣ Empty 2 Empty 4) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  have hf2 : (Semiterm.val ![x,insert b a,b,a] Empty.elim ∘ (Rew.subst ![#0,#3] : Rew ℒₒᵣ Empty 2 Empty 4) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv1,hv2,hf1,hf2]
  have h1 : bitDef.val.Evalb ![x,insert b a] ↔ x ∈ insert b a := by simpa using bit_defined.defined ![x,insert b a]
  have h2 : bitDef.val.Evalb ![x,a] ↔ x ∈ a := by simpa using bit_defined.defined ![x,a]
  simpa [Semiformula.Evalb,h1,h2,or_comm] using (mem_insert (a := x) (b := b) (c := a))
theorem PA_proves_insert : (𝗣𝗔 : ArithmeticTheory) ⊢ insertSentence := Entailment.WeakerThan.pbl ISigma1_proves_insert

section model
open LO.FirstOrder.Arithmetic.Bootstrapping
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma internal_PA_insert (a b : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      (⌜(∃⁰ ∀⁰ insertCore : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.fvar b,Bootstrapping.Semiterm.fvar a] := by
  let d := PA_proves_insert.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜insertSentence⌝ : V) := ⟨⌜d⌝, proof_of_quote_proof d⟩
  have he : (⌜insertSentence⌝ : V) = ^∀ ^∀ (⌜(∃⁰ ∀⁰ insertCore : ArithmeticSemisentence 2)⌝ : V) := by
    rw [Sentence.quote_def, insertSentence, Rewriting.app_all, Rew.q_emb, Semiformula.quote_all,
      Rewriting.app_all, Rew.q_emb, Semiformula.quote_all, ← Sentence.quote_def]
  rw [he] at hb
  have ht : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∀⁰ ∀⁰ (⌜(∃⁰ ∀⁰ insertCore : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) :=
    (tprovable_iff_provable).mpr hb
  exact TProof.specialize₂! ht (Bootstrapping.Semiterm.fvar b) (Bootstrapping.Semiterm.fvar a)

lemma insert_subst_shape (a b : V) :
    (⌜(∃⁰ ∀⁰ insertCore : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.fvar b,Bootstrapping.Semiterm.fvar a] =
      ∃⁰ ∀⁰ (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
          ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1]) 🡘
        (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
          ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) ⋎
         ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar b))) := by
  have hemb1 : (Rewriting.emb (bitDef.val ⇜ ![#0,#1]) : ArithmeticSemiformula Nat 4) =
      (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) ⇜ ![#0,#1] := by
    rw [Semiformula.coe_subst_eq_subst_coe]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hemb2 : (Rewriting.emb (bitDef.val ⇜ ![#0,#3]) : ArithmeticSemiformula Nat 4) =
      (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) ⇜ ![#0,#3] := by
    rw [Semiformula.coe_subst_eq_subst_coe]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  simp [Sentence.typed_quote_def,insertCore,hemb1,hemb2,Semiformula.typed_quote_substs,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]

lemma internal_PA_insert_explicit (a b : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∃⁰ ∀⁰ (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
          ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.bvar 1]) 🡘
        (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
          ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) ⋎
         ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar b))) := by
  rw [← insert_subst_shape]
  exact internal_PA_insert a b

#print axioms internal_PA_insert_explicit
#print axioms insert_subst_shape
#print axioms internal_PA_insert
end model
#print axioms ISigma1_proves_insert
end PA194InternalBitInsert
