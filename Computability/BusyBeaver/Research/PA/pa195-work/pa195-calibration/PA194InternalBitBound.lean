import PA194InternalSingleton
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194InternalBitBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
@[irreducible] def core : ArithmeticSemisentence 2 :=
  (bitDef.val ⇜ ![#0,#1]) 🡒 “#0 < #1”
def sentence : ArithmeticSentence := ∀⁰ ∀⁰ core

theorem isigma1_proves : (𝗜𝚺₁ : ArithmeticTheory) ⊢ sentence := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff,sentence,Semiformula.eval_all]
  intro a x
  simp only [core,LogicalConnective.HomClass.map_imply]
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val ![x,a] Empty.elim ∘ (Rew.subst ![#0,#1] : Rew ℒₒᵣ Empty 2 Empty 2) ∘ Semiterm.bvar) = ![x,a] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hf : (Semiterm.val ![x,a] Empty.elim ∘ (Rew.subst ![#0,#1] : Rew ℒₒᵣ Empty 2 Empty 2) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  have hbit : bitDef.val.Evalb ![x,a] ↔ x ∈ a := by simpa using bit_defined.defined ![x,a]
  intro h
  have hm : x ∈ a := hbit.mp h
  simpa using (lt_of_mem hm)
theorem PA_proves : (𝗣𝗔 : ArithmeticTheory) ⊢ sentence := Entailment.WeakerThan.pbl isigma1_proves
section model
open LO.FirstOrder.Arithmetic.Bootstrapping
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma internal_PA_bound (a : V) : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
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
  simpa [SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using TProof.specialize! ht (Bootstrapping.Semiterm.fvar a)
lemma core_shape (a : V) :
    (⌜core⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![(Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1), Bootstrapping.Semiterm.fvar a] =
    (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) 🡒
      ((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a])) := by
  have hemb : (Rewriting.emb (bitDef.val ⇜ ![#0,#1]) : ArithmeticSemiformula Nat 2) =
      (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) ⇜ ![#0,#1] := by
    rw [Semiformula.coe_subst_eq_subst_coe]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  simp [Sentence.typed_quote_def,core,hemb,Semiformula.typed_quote_substs,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail]
lemma internal_PA_bound_explicit (a : V) : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ (((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a]) 🡒
      ((⌜(“#0 < #1” : ArithmeticSemisentence 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Semiterm.fvar a])) := by
  simpa [core_shape] using internal_PA_bound a
#print axioms internal_PA_bound_explicit
#print axioms isigma1_proves
end model
end PA194InternalBitBound
