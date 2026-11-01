import DiophantineConsistency.IPRATwoImpLogic
set_option autoImplicit false
namespace DiophantineConsistency.IPRAEqualityTransGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRALanguage PRATheory IPRANativeTheory
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def matrix : Semisentenceᵢ language 2 := Semiformulaᵢ.rel Language.ORing.Rel.eq ![#1,#0]
def ax : Propositionᵢ language := Rewriting.emb (eqSubstitutionI matrix)
def e {n : ℕ} (x y : Semiterm language ℕ n) : Semiformulaᵢ language ℕ n := Semiformulaᵢ.rel Language.ORing.Rel.eq ![x,y]

theorem trans_open_rev : [ax] ⊢[𝗜𝗻𝘁¹] e &2 &1 🡒 e &1 &0 🡒 e &2 &0 := by
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [e &1 &0, e &2 &1, ax]
  have hy : Γ ⊢[𝗜𝗻𝘁¹]! e &1 &0 := FiniteContext.byAxm₀
  have hx : Γ ⊢[𝗜𝗻𝘁¹]! e &2 &1 := FiniteContext.byAxm₁
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! ax := FiniteContext.byAxm₂
  have ht := HilbertProofᵢ.specializeOverContext ha (&2 : SyntacticTerm language)
  have ht' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ ∀⁰ (e #0 #1 🡒 e &2 #0 🡒 e &2 #1) := by
    convert ht using 1
    simp [e, matrix, eqLeft, eqRight, Semiformulaᵢ.rewAux,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht2 := HilbertProofᵢ.specializeOverContext ht' (&0 : SyntacticTerm language)
  have ht2' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ (e #0 &0 🡒 e &2 #0 🡒 e &2 &0) := by
    convert ht2 using 1
    simp [e, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht3 := HilbertProofᵢ.specializeOverContext ht2' (&1 : SyntacticTerm language)
  have ht3' : Γ ⊢[𝗜𝗻𝘁¹]! e &1 &0 🡒 e &2 &1 🡒 e &2 &0 := by
    convert ht3 using 1
    simp [e, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  exact ⟨(ht3' ⨀ hy) ⨀ hx⟩
theorem trans_closed_context : [ax] ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ ∀⁰
    (e #2 #1 🡒 e #1 #0 🡒 e #2 #0) := by
  let Γ : List (Propositionᵢ language) := [ax]
  have hΓ : Γ⁺ = Γ := by
    simp [Γ, ax]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  have ho := Classical.choice trans_open_rev
  convert ho using 1
  simp [e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rewriting.free, Function.comp_def]
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
def transI : Sentenceᵢ language := ∀⁰ ∀⁰ ∀⁰
  ((Semiformulaᵢ.rel Language.ORing.Rel.eq ![#2,#1]) 🡒
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#1,#0]) 🡒 Semiformulaᵢ.rel Language.ORing.Rel.eq ![#2,#0])

theorem trans_native : nativeTheory ⊢ transI := by
  let Γ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : Γ *⊢[𝗜𝗻𝘁¹] ax := by
    exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution matrix))
  have hc : Γ *⊢[𝗜𝗻𝘁¹] ⋀[ax] := by
    apply Conj₂!_iff_forall_provable.mpr
    intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    exact hax
  have hi : Γ *⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ ∀⁰ (e #2 #1 🡒 e #1 #0 🡒 e #2 #0) :=
    ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice trans_closed_context)))
      (Classical.choice hc)⟩
  change Γ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb transI : Propositionᵢ language)
  convert hi using 1
  simp [transI, e, Semiformulaᵢ.rew_rel]
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
theorem trans_image : nativeTheory ⊢ (Theory.Eq.trans language)ᴺ := by
  have himp := IPRATwoImpLogic.atomic_twoImp_closure (n := 3)
    Language.ORing.Rel.eq Language.ORing.Rel.eq Language.ORing.Rel.eq
    ![#2,#1] ![#1,#0] ![#2,#0]
  have hn : nativeTheory ⊢
      (∀⁰* ((Semiformulaᵢ.rel Language.ORing.Rel.eq ![#2,#1]) 🡒
        (Semiformulaᵢ.rel Language.ORing.Rel.eq ![#1,#0]) 🡒 Semiformulaᵢ.rel Language.ORing.Rel.eq ![#2,#0] : Semisentenceᵢ language 3)) := by
    simpa [transI, allClosure_succ] using trans_native
  have ht := mdp! himp hn
  change nativeTheory ⊢ (∀⁰ ∀⁰ ∀⁰
    ((Semiformula.rel Language.ORing.Rel.eq ![#2,#1]) 🡒
      (Semiformula.rel Language.ORing.Rel.eq ![#1,#0]) 🡒 Semiformula.rel Language.ORing.Rel.eq ![#2,#0]))ᴺ
  simpa [allClosure_succ] using ht
end DiophantineConsistency.IPRAEqualityTransGG
