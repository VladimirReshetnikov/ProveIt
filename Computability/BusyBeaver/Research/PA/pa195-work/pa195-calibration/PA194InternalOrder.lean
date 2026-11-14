import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194InternalOrder
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
@[irreducible] def core : ArithmeticSemisentence 2 :=
  (“#0 < #1 + 1” 🡘 (“#0 < #1” ⋎ op(=).operator ![#0,#1]))
def sentence : ArithmeticSentence := ∀⁰ ∀⁰ core

theorem isigma1_proves : (𝗜𝚺₁ : ArithmeticTheory) ⊢ sentence := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff,sentence,Semiformula.eval_all]
  intro a x
  simp [core,lt_succ_iff_le,le_iff_lt_or_eq]
@[irreducible] def zeroCore : ArithmeticSemisentence 1 := ∼(“#0 < 0”)
def zeroSentence : ArithmeticSentence := ∀⁰ zeroCore

theorem isigma1_proves_zero : (𝗜𝚺₁ : ArithmeticTheory) ⊢ zeroSentence := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp [models_iff,zeroSentence,zeroCore,Semiformula.eval_all]
theorem PA_proves_zero : (𝗣𝗔 : ArithmeticTheory) ⊢ zeroSentence := Entailment.WeakerThan.pbl isigma1_proves_zero

theorem PA_proves : (𝗣𝗔 : ArithmeticTheory) ⊢ sentence := Entailment.WeakerThan.pbl isigma1_proves
section model
open LO.FirstOrder.Arithmetic.Bootstrapping
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma internal_PA_zero : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ (⌜zeroCore⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) := by
  let d := PA_proves_zero.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜zeroSentence⌝ : V) := ⟨⌜d⌝, proof_of_quote_proof d⟩
  have he : (⌜zeroSentence⌝ : V) = ^∀ (⌜zeroCore⌝ : V) := by
    rw [Sentence.quote_def,zeroSentence,Rewriting.app_all,Rew.q_emb,Semiformula.quote_all,←Sentence.quote_def]
  rw [he] at hb
  exact (tprovable_iff_provable).mpr hb
lemma zero_shape : (⌜zeroCore⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) =
    ∼((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Arithmetic.typedNumeral 0]) := by
  simp [Sentence.typed_quote_def,zeroCore,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]
lemma internal_PA_order (a : V) : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ ((⌜core⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) := by
  let d := PA_proves.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜sentence⌝ : V) := ⟨⌜d⌝, proof_of_quote_proof d⟩
  have he : (⌜sentence⌝ : V) = ^∀ ^∀ (⌜core⌝ : V) := by
    rw [Sentence.quote_def,sentence,Rewriting.app_all,Rew.q_emb,Semiformula.quote_all,
      Rewriting.app_all,Rew.q_emb,Semiformula.quote_all,←Sentence.quote_def]
  rw [he] at hb
  have ht : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
      ∀⁰ ∀⁰ (⌜core⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2) := (tprovable_iff_provable).mpr hb
  simpa [SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using
    TProof.specialize! ht (Bootstrapping.Semiterm.fvar a)
lemma core_shape (a : V) :
    (⌜core⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a] =
    (((⌜(“#0 < #1 + 1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) 🡘
      (((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) ⋎
       ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a))) := by
  simp [Sentence.typed_quote_def,core,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]
lemma lt_succ_template (a : V) :
    (⌜(“#0 < #1 + 1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![(Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1), Bootstrapping.Semiterm.fvar a] =
    (⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0,
        (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1).subst
          ![Bootstrapping.Semiterm.fvar a]] := by
  simp [Sentence.typed_quote_def, SemitermVec.q,Matrix.vecHead,Matrix.vecTail]
lemma internal_PA_order_explicit (a : V) : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ (((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0,
        (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1).subst ![Bootstrapping.Semiterm.fvar a]]) 🡘
     (((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar a]) ⋎
      ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a))) := by
  simpa [core_shape,lt_succ_template] using internal_PA_order a
lemma internal_PA_zero_explicit : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ ∼((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Arithmetic.typedNumeral 0]) := by
  simpa [zero_shape] using (internal_PA_zero (V := V))
#print axioms internal_PA_order_explicit
#print axioms internal_PA_zero_explicit
#print axioms zero_shape
#print axioms internal_PA_zero
#print axioms lt_succ_template
#print axioms core_shape
#print axioms internal_PA_order
end model
#print axioms isigma1_proves
end PA194InternalOrder
