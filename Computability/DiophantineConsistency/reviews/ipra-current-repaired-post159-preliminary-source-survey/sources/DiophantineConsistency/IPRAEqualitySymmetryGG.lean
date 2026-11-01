import DiophantineConsistency.IPRANativeEquationImages
import DiophantineConsistency.IPRANativeBasicImages
/-! Derive native equality symmetry from actual native reflexivity and one
closed Leibniz substitution axiom, then prove the actual classical GG image. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAEqualitySymmetryGG
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

def matrix : Semisentenceᵢ language 2 := Semiformulaᵢ.rel .eq ![#0,#1]
def ax : Propositionᵢ language := Rewriting.emb (eqSubstitutionI matrix)
def reflAx : Propositionᵢ language := Rewriting.emb eqReflI

def e {n : ℕ} (x y : Semiterm language ℕ n) : Semiformulaᵢ language ℕ n := Semiformulaᵢ.rel .eq ![x,y]

theorem symmetry_open : [ax,reflAx] ⊢[𝗜𝗻𝘁¹] e &0 &1 🡒 e &1 &0 := by
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [e &0 &1, ax, reflAx]
  have hx : Γ ⊢[𝗜𝗻𝘁¹]! e &0 &1 := FiniteContext.byAxm₀
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! ax := FiniteContext.byAxm₁
  have hr : Γ ⊢[𝗜𝗻𝘁¹]! reflAx := FiniteContext.byAxm₂
  have ht := HilbertProofᵢ.specializeOverContext ha (&0 : SyntacticTerm language)
  have ht' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ ∀⁰ (e #0 #1 🡒 e #0 &0 🡒 e #1 &0) := by
    convert ht using 1
    simp [e, matrix, eqLeft, eqRight, Semiformulaᵢ.rewAux,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht2 := HilbertProofᵢ.specializeOverContext ht' (&1 : SyntacticTerm language)
  have ht2' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ (e #0 &1 🡒 e #0 &0 🡒 e &1 &0) := by
    convert ht2 using 1
    simp [e, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht3 := HilbertProofᵢ.specializeOverContext ht2' (&0 : SyntacticTerm language)
  have ht3' : Γ ⊢[𝗜𝗻𝘁¹]! e &0 &1 🡒 e &0 &0 🡒 e &1 &0 := by
    convert ht3 using 1
    simp [e, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have hr0 := HilbertProofᵢ.specializeOverContext hr (&0 : SyntacticTerm language)
  have hr0' : Γ ⊢[𝗜𝗻𝘁¹]! e &0 &0 := by
    convert hr0 using 1
    simp [e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  exact ⟨(ht3' ⨀ hx) ⨀ hr0'⟩
theorem symmetry_open_swapped : [ax,reflAx] ⊢[𝗜𝗻𝘁¹] e &1 &0 🡒 e &0 &1 := by
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [e &1 &0, ax, reflAx]
  have hx : Γ ⊢[𝗜𝗻𝘁¹]! e &1 &0 := FiniteContext.byAxm₀
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! ax := FiniteContext.byAxm₁
  have hr : Γ ⊢[𝗜𝗻𝘁¹]! reflAx := FiniteContext.byAxm₂
  have ht := HilbertProofᵢ.specializeOverContext ha (&1 : SyntacticTerm language)
  have ht' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ ∀⁰ (e #0 #1 🡒 e #0 &1 🡒 e #1 &1) := by
    convert ht using 1
    simp [e, matrix, eqLeft, eqRight, Semiformulaᵢ.rewAux,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht2 := HilbertProofᵢ.specializeOverContext ht' (&0 : SyntacticTerm language)
  have ht2' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ (e #0 &0 🡒 e #0 &1 🡒 e &0 &1) := by
    convert ht2 using 1
    simp [e, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht3 := HilbertProofᵢ.specializeOverContext ht2' (&1 : SyntacticTerm language)
  have ht3' : Γ ⊢[𝗜𝗻𝘁¹]! e &1 &0 🡒 e &1 &1 🡒 e &0 &1 := by
    convert ht3 using 1
    simp [e, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have hr0 := HilbertProofᵢ.specializeOverContext hr (&1 : SyntacticTerm language)
  have hr0' : Γ ⊢[𝗜𝗻𝘁¹]! e &1 &1 := by
    convert hr0 using 1
    simp [e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  exact ⟨(ht3' ⨀ hx) ⨀ hr0'⟩
theorem symmetry_closed_context : [ax,reflAx] ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ (e #1 #0 🡒 e #0 #1) := by
  let Γ : List (Propositionᵢ language) := [ax,reflAx]
  have hΓ : Γ⁺ = Γ := by
    simp [Γ, ax, reflAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  have ho := Classical.choice symmetry_open_swapped
  convert ho using 1
  simp [e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rewriting.free, Function.comp_def]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
def symmI : Sentenceᵢ language := ∀⁰ ∀⁰
  ((Semiformulaᵢ.rel .eq ![#1,#0]) 🡒 (Semiformulaᵢ.rel .eq ![#0,#1]))

theorem symmetry_native : nativeTheory ⊢ symmI := by
  let Γ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : Γ *⊢[𝗜𝗻𝘁¹] ax := by
    exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution matrix))
  have hr : Γ *⊢[𝗜𝗻𝘁¹] reflAx := by
    exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
  have hc : Γ *⊢[𝗜𝗻𝘁¹] ⋀[ax,reflAx] := by
    apply Conj₂!_iff_forall_provable.mpr
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hax
    · exact hr
  have hi : Γ *⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ (e #1 #0 🡒 e #0 #1) :=
    ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice symmetry_closed_context)))
      (Classical.choice hc)⟩
  change Γ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb symmI : Propositionᵢ language)
  convert hi using 1
  simp [symmI, e, Semiformulaᵢ.rew_rel]
  constructor <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
theorem symmetry_image : nativeTheory ⊢ (Theory.Eq.symm language)ᴺ := by
  have h := IPRANativeBasicImages.atomic_imp_closure (n := 2)
    Language.ORing.Rel.eq Language.ORing.Rel.eq ![#1,#0] ![#0,#1]
  have hh := Entailment.mdp! h symmetry_native
  change nativeTheory ⊢ (∀⁰* (((Semiformula.rel Language.ORing.Rel.eq ![#1,#0]) 🡒
    Semiformula.rel Language.ORing.Rel.eq ![#0,#1]) : Semisentence language 2))ᴺ at hh
  change nativeTheory ⊢ (∀⁰* (((Semiformula.rel Language.ORing.Rel.eq ![#1,#0]) 🡒
    Semiformula.rel Language.ORing.Rel.eq ![#0,#1]) : Semisentence language 2))ᴺ
  exact hh
end DiophantineConsistency.IPRAEqualitySymmetryGG
