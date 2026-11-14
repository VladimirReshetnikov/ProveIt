import PA194InternalSingleton
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194InternalEmpty
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
@[irreducible] def emptyCore : ArithmeticSemisentence 1 := ∼(bitDef.val ⇜ ![#0,‘0’])
def emptySentence : ArithmeticSentence := ∀⁰ emptyCore

theorem ISigma1_proves_empty : (𝗜𝚺₁ : ArithmeticTheory) ⊢ emptySentence := by
  apply Arithmetic.complete.{0}
  intro M _ _
  simp only [models_iff, emptySentence, Semiformula.eval_all]
  intro x
  simp only [emptyCore, LogicalConnective.HomClass.map_neg]
  rw [Semiformula.eval_rew]
  have hv : (Semiterm.val ![x] Empty.elim ∘ (Rew.subst ![#0,‘0’] : Rew ℒₒᵣ Empty 2 Empty 1) ∘ Semiterm.bvar) = ![x,(0:M)] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hf : (Semiterm.val ![x] Empty.elim ∘ (Rew.subst ![#0,‘0’] : Rew ℒₒᵣ Empty 2 Empty 1) ∘ Semiterm.fvar) = (Empty.elim : Empty → M) := Subsingleton.elim _ _
  rw [hv,hf]
  have hbit : bitDef.val.Evalb ![x,(0:M)] ↔ x ∈ (∅:M) := by simpa using bit_defined.defined ![x,(0:M)]
  change ¬ bitDef.val.Evalb ![x,(0:M)]
  rw [hbit]
  exact not_mem_empty x

theorem PA_proves_empty : (𝗣𝗔 : ArithmeticTheory) ⊢ emptySentence := Entailment.WeakerThan.pbl ISigma1_proves_empty
section model
open LO.FirstOrder.Arithmetic.Bootstrapping
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
lemma internal_PA_empty : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ (⌜emptyCore⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) := by
  let b := PA_proves_empty.some
  have hb : Provable (𝗣𝗔 : ArithmeticTheory) (⌜emptySentence⌝ : V) := ⟨⌜b⌝,proof_of_quote_proof b⟩
  have he : (⌜emptySentence⌝ : V) = ^∀ (⌜emptyCore⌝ : V) := by
    rw [Sentence.quote_def, emptySentence, Rewriting.app_all, Rew.q_emb, Semiformula.quote_all, ← Sentence.quote_def]
  apply (tprovable_iff_provable).mpr
  rw [he] at hb
  exact hb
lemma empty_core_shape :
    (⌜emptyCore⌝ : Bootstrapping.Semiformula V ℒₒᵣ 1) =
      ∼((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
        ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Arithmetic.typedNumeral 0]) := by
  have hemb : (Rewriting.emb (bitDef.val ⇜ ![#0,‘0’]) : ArithmeticSemiformula Nat 1) =
      (Rewriting.emb bitDef.val : ArithmeticSemiformula Nat 2) ⇜ ![#0,‘0’] := by
    rw [Semiformula.coe_subst_eq_subst_coe]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  have hv : (fun i : Fin 2 => (⌜(![#0,‘0’] : Fin 2 → ArithmeticSemiterm Nat 1) i⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1)) =
      ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Arithmetic.typedNumeral 0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact Fin.cases (by simp) (fun j => Fin.elim0 j) j
  simp [Sentence.typed_quote_def,emptyCore,hemb, Semiformula.typed_quote_substs, hv]

lemma internal_PA_empty_explicit : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢
    ∀⁰ ∼((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst
      ![Bootstrapping.Semiterm.bvar 0, Bootstrapping.Arithmetic.typedNumeral 0]) := by
  rw [←empty_core_shape]
  exact internal_PA_empty

#print axioms internal_PA_empty_explicit
#print axioms internal_PA_empty
end model
#print axioms ISigma1_proves_empty
end PA194InternalEmpty
