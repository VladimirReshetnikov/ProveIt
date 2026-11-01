import DiophantineConsistency.IPRANativeBasicImages
/-! Native binary-relation transport from two actual Leibniz axioms. This is
not yet the GG image of Foundation's conjunction-shaped relation axiom. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRABinaryRelationNative
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

def atom {n : ℕ} (r : language.Rel 2) (x y : Semiterm language ℕ n) : Semiformulaᵢ language ℕ n :=
  Semiformulaᵢ.rel r ![x,y]
def eq {n : ℕ} (x y : Semiterm language ℕ n) : Semiformulaᵢ language ℕ n := atom .eq x y
def matrixL (r : language.Rel 2) : Semisentenceᵢ language 2 := Semiformulaᵢ.rel r ![#0,#1]
def axL (r : language.Rel 2) : Propositionᵢ language := Rewriting.emb (eqSubstitutionI (matrixL r))
def matrixR (r : language.Rel 2) : Semisentenceᵢ language 2 := Semiformulaᵢ.rel r ![#1,#0]
def axR (r : language.Rel 2) : Propositionᵢ language := Rewriting.emb (eqSubstitutionI (matrixR r))

theorem rel_left_open (r : language.Rel 2) (x y z : ℕ) :
    [axL r] ⊢[𝗜𝗻𝘁¹] eq &x &y 🡒 atom r &x &z 🡒 atom r &y &z := by
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [atom r &x &z, eq &x &y, axL r]
  have hr : Γ ⊢[𝗜𝗻𝘁¹]! atom r &x &z := FiniteContext.byAxm₀
  have he : Γ ⊢[𝗜𝗻𝘁¹]! eq &x &y := FiniteContext.byAxm₁
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! axL r := FiniteContext.byAxm₂
  have ht := HilbertProofᵢ.specializeOverContext ha (&z : SyntacticTerm language)
  have ht' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ ∀⁰ (eq #0 #1 🡒 atom r #0 &z 🡒 atom r #1 &z) := by
    convert ht using 1
    simp [atom, eq, matrixL, eqLeft, eqRight, Semiformulaᵢ.rewAux,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht2 := HilbertProofᵢ.specializeOverContext ht' (&y : SyntacticTerm language)
  have ht2' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ (eq #0 &y 🡒 atom r #0 &z 🡒 atom r &y &z) := by
    convert ht2 using 1
    simp [atom, eq, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht3 := HilbertProofᵢ.specializeOverContext ht2' (&x : SyntacticTerm language)
  have ht3' : Γ ⊢[𝗜𝗻𝘁¹]! eq &x &y 🡒 atom r &x &z 🡒 atom r &y &z := by
    convert ht3 using 1
    simp [atom, eq, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  exact ⟨(ht3' ⨀ he) ⨀ hr⟩
theorem rel_right_open (r : language.Rel 2) (x y z : ℕ) :
    [axR r] ⊢[𝗜𝗻𝘁¹] eq &x &y 🡒 atom r &z &x 🡒 atom r &z &y := by
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [atom r &z &x, eq &x &y, axR r]
  have hr : Γ ⊢[𝗜𝗻𝘁¹]! atom r &z &x := FiniteContext.byAxm₀
  have he : Γ ⊢[𝗜𝗻𝘁¹]! eq &x &y := FiniteContext.byAxm₁
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! axR r := FiniteContext.byAxm₂
  have ht := HilbertProofᵢ.specializeOverContext ha (&z : SyntacticTerm language)
  have ht' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ ∀⁰ (eq #0 #1 🡒 atom r &z #0 🡒 atom r &z #1) := by
    convert ht using 1
    simp [atom, eq, matrixR, eqLeft, eqRight, Semiformulaᵢ.rewAux,
      Semiformulaᵢ.rew_rel, Rewriting.subst, Function.comp_def]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht2 := HilbertProofᵢ.specializeOverContext ht' (&y : SyntacticTerm language)
  have ht2' : Γ ⊢[𝗜𝗻𝘁¹]! ∀⁰ (eq #0 &y 🡒 atom r &z #0 🡒 atom r &z &y) := by
    convert ht2 using 1
    simp [atom, eq, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  have ht3 := HilbertProofᵢ.specializeOverContext ht2' (&x : SyntacticTerm language)
  have ht3' : Γ ⊢[𝗜𝗻𝘁¹]! eq &x &y 🡒 atom r &z &x 🡒 atom r &z &y := by
    convert ht3 using 1
    simp [atom, eq, Semiformulaᵢ.rew_rel, Rewriting.subst]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  exact ⟨(ht3' ⨀ he) ⨀ hr⟩
theorem relation_open (r : language.Rel 2) (x y u v : ℕ) :
    [axL r, axR r] ⊢[𝗜𝗻𝘁¹]
      eq &x &u 🡒 eq &y &v 🡒 atom r &x &y 🡒 atom r &u &v := by
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  apply FiniteContext.deduct!
  let Γ : List (Propositionᵢ language) := [atom r &x &y, eq &y &v, eq &x &u, axL r, axR r]
  have ha : Γ ⊢[𝗜𝗻𝘁¹]! atom r &x &y := FiniteContext.byAxm₀
  have hb : Γ ⊢[𝗜𝗻𝘁¹]! eq &y &v := FiniteContext.byAxm₁
  have hc : Γ ⊢[𝗜𝗻𝘁¹]! eq &x &u := FiniteContext.byAxm₂
  have hL : Γ ⊢[𝗜𝗻𝘁¹]! eq &x &u 🡒 atom r &x &y 🡒 atom r &u &y :=
    FiniteContext.weakening (by simp [Γ]) (Classical.choice (rel_left_open r x u y))
  have hR : Γ ⊢[𝗜𝗻𝘁¹]! eq &y &v 🡒 atom r &u &y 🡒 atom r &u &v :=
    FiniteContext.weakening (by simp [Γ]) (Classical.choice (rel_right_open r y v u))
  exact ⟨(hR ⨀ hb) ⨀ ((hL ⨀ hc) ⨀ ha)⟩
theorem relation_closed_context (r : language.Rel 2) :
    [axL r, axR r] ⊢[𝗜𝗻𝘁¹]
      ∀⁰ ∀⁰ ∀⁰ ∀⁰ (eq #0 #2 🡒 eq #1 #3 🡒 atom r #0 #1 🡒 atom r #2 #3) := by
  let Γ : List (Propositionᵢ language) := [axL r, axR r]
  have hΓ : Γ⁺ = Γ := by simp [Γ, axL, axR]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΓ]
  have ho := Classical.choice (relation_open r 0 1 2 3)
  convert ho using 1
  simp [atom, eq, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel,
    Rewriting.free, Function.comp_def]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
def relationI (r : language.Rel 2) : Sentenceᵢ language := ∀⁰ ∀⁰ ∀⁰ ∀⁰
    ((Semiformulaᵢ.rel .eq ![#0,#2]) 🡒 (Semiformulaᵢ.rel .eq ![#1,#3]) 🡒
      Semiformulaᵢ.rel r ![#0,#1] 🡒 Semiformulaᵢ.rel r ![#2,#3])

theorem relation_native (r : language.Rel 2) : nativeTheory ⊢ relationI r := by
  let Γ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hL : Γ *⊢[𝗜𝗻𝘁¹] axL r := by
    exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (matrixL r)))
  have hR : Γ *⊢[𝗜𝗻𝘁¹] axR r := by
    exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (matrixR r)))
  have hc : Γ *⊢[𝗜𝗻𝘁¹] ⋀[axL r,axR r] := by
    apply Conj₂!_iff_forall_provable.mpr
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact hL
    · exact hR
  have hi : Γ *⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ ∀⁰ ∀⁰
      (eq #0 #2 🡒 eq #1 #3 🡒 atom r #0 #1 🡒 atom r #2 #3) :=
    ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice (relation_closed_context r))))
      (Classical.choice hc)⟩
  change Γ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb (relationI r) : Propositionᵢ language)
  convert hi using 1
  simp [relationI, atom, eq, Semiformulaᵢ.rew_rel]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
  | zero => rfl
  | succ j => cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
end DiophantineConsistency.IPRABinaryRelationNative
