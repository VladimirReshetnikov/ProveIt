import DiophantineConsistency.IPRAZeroLeft
set_option autoImplicit false
namespace DiophantineConsistency.IPRASuccLeft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRAPredReconstruct IPRAAddRecursion IPRAZeroLeft
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def IH₂ (a b : SyntacticTerm language) : Propositionᵢ language := equal (add (sc a) b) (sc (add a b))
def C₂ (a b : SyntacticTerm language) : List (Propositionᵢ language) := IH₂ a b :: D
theorem lift_delta {φ : Propositionᵢ language} (h : Δ ⊢[𝗜𝗻𝘁¹] φ) (a b : SyntacticTerm language) : C₂ a b ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro p hp; simp [C₂, D, hp]) (Classical.choice h)⟩
theorem trans_new {a b c d e : SyntacticTerm language} (h : C₂ a b ⊢[𝗜𝗻𝘁¹] equal c d)
    (j : C₂ a b ⊢[𝗜𝗻𝘁¹] equal d e) : C₂ a b ⊢[𝗜𝗻𝘁¹] equal c e := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context (C₂ a b) (by simp [C₂, D, Δ, Γ]) c d e) h) j
theorem congr_succ {a b c d : SyntacticTerm language} (h : C₂ a b ⊢[𝗜𝗻𝘁¹] equal c d) : C₂ a b ⊢[𝗜𝗻𝘁¹] equal (sc c) (sc d) := by
  have hx : ∀ i : Fin 1, funAx Code.succ i ∈ C₂ a b := by
    intro i; cases i using Fin.cases with
    | zero => simp [C₂, D, Δ, Γ]
    | succ i => exact Fin.elim0 i
  exact function_open_in_context Code.succ (C₂ a b) (by simp [C₂,D,Δ,Γ]) (by simp [C₂,D,Δ,Γ]) hx _ _ (fun _ => h)
theorem congr_add {a b c d e f : SyntacticTerm language}
    (h : C₂ a b ⊢[𝗜𝗻𝘁¹] equal c d) (j : C₂ a b ⊢[𝗜𝗻𝘁¹] equal e f) :
    C₂ a b ⊢[𝗜𝗻𝘁¹] equal (add c e) (add d f) := by
  have hx : ∀ i : Fin 2, funAx addCode i ∈ C₂ a b := by
    intro i; cases i using Fin.cases with
    | zero => simp [C₂,D]
    | succ i => cases i using Fin.cases with
      | zero => simp [C₂,D]
      | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 2, C₂ a b ⊢[𝗜𝗻𝘁¹] equal (![c,e] i) (![d,f] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context addCode (C₂ a b) (by simp [C₂,D,Δ,Γ]) (by simp [C₂,D,Δ,Γ]) hx _ _ hr

theorem step_open (a b : SyntacticTerm language) : C₂ a b ⊢[𝗜𝗻𝘁¹] IH₂ a (add b one) := by
  have ih : C₂ a b ⊢[𝗜𝗻𝘁¹] IH₂ a b := ⟨FiniteContext.byAxm (by simp [C₂])⟩
  have hone := lift_delta (lift_old (add_one_open b)) a b
  have hone' := Entailment.mdp! (lift_delta (symm_new _ _) a b) hone
  have hz : C₂ a b ⊢[𝗜𝗻𝘁¹] equal (sc a) (sc a) := refl_context (C₂ a b) (by simp [C₂,D,Δ,Γ]) (sc a)
  have ha : C₂ a b ⊢[𝗜𝗻𝘁¹] equal a a := refl_context (C₂ a b) (by simp [C₂,D,Δ,Γ]) a
  have hr := lift_delta (add_succ_open a b) a b
  have hr' := Entailment.mdp! (lift_delta (symm_new _ _) a b) hr
  exact trans_new (congr_add hz hone)
    (trans_new (lift_delta (add_succ_open (sc a) b) a b)
      (trans_new (congr_succ ih) (trans_new (congr_succ hr') (congr_succ (congr_add ha hone')))))
theorem base_open (a : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] IH₂ a z := by
  have h := add_zero_open (sc a)
  have j := IPRAPredReconstruct.congr_succ (add_zero_open a)
  exact IPRAPredReconstruct.trans_new h (Entailment.mdp! (symm_new _ _) j)
def matrix : Semisentenceᵢ language 2 := .rel .eq
  ![.func addCode ![.func .succ (fun _ => #1),#0], .func .succ (fun _ => .func addCode ![#1,#0])]
theorem matrix_open : IPRAQuantifierFree.OpenI matrix := by simp [matrix, IPRAQuantifierFree.OpenI]

theorem var_zero : Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = (&0 : SyntacticTerm language) := by
  rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
theorem var_one : Rew.free (Rew.free (#(1 : Fin 2) : Semiterm language ℕ 2)) = (&1 : SyntacticTerm language) := by
  change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
  rw [Rew.free_bvar_last, Rew.free_fvar]

theorem matrix_free2 : Rewriting.free (Rewriting.free (Rewriting.emb matrix)) = IH₂ (&1) (&0) := by
  simp [matrix, IH₂, add, sc, equal, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, var_one]
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, var_one]
    | succ i => exact Fin.elim0 i

theorem matrix_step_free2 : Rewriting.free (Rewriting.free (Rewriting.emb (atStep matrix))) = IH₂ (&1) (add (&0) one) := by
  simp [matrix, IH₂, add, sc, one, equal, atStep, stepTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff]
    change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
    exact var_one
  | succ i => cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff]
      change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
      exact var_one
    | succ i => exact Fin.elim0 i
theorem step_closed : D ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰ (Rewriting.emb matrix 🡒 Rewriting.emb (atStep matrix)) := by
  have hD : D⁺ = D := by simp [D, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hD]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hD]
  have ho := Classical.choice (FiniteContext.deduct! (step_open (&1) (&0)))
  convert ho using 1
  have h1 := matrix_free2
  have h2 := matrix_step_free2
  simp [matrix, IH₂, add, sc, equal, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel] at h1
  simp [matrix, IH₂, add, sc, one, equal, atStep, stepTerm, Rewriting.free, Rewriting.emb, Semiformulaᵢ.rew_rel] at h2
  simpa [matrix, IH₂, add, sc, one, equal, atStep, stepTerm, Rewriting.free, Rewriting.emb,
    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def] using And.intro h1 h2
theorem base_closed : D ⊢[𝗜𝗻𝘁¹] ∀⁰ Rewriting.emb (atZero matrix) := by
  have hD : D⁺ = D := by simp [D, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hD]
  have ho : D ⊢[𝗜𝗻𝘁¹] IH₂ (&0) z := by
    apply Nonempty.intro
    apply FiniteContext.weakening (Γ := Δ)
    · intro p hp; simp [D, hp]
    · exact Classical.choice (base_open (&0))
  convert Classical.choice ho using 1
  simp [matrix, IH₂, add, sc, z, equal, atZero, zeroTerm, Rewriting.free, Rewriting.emb,
    Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff]
    change Rew.free (#(0 : Fin 1) : Semiterm language ℕ 1) = &0
    rw [Rew.free_bvar_last_zero]
  | succ i => cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two, funext_iff]
      change Rew.free (#(0 : Fin 1) : Semiterm language ℕ 1) = &0
      rw [Rew.free_bvar_last_zero]
    | succ i => exact Fin.elim0 i
theorem base_native : nativeTheory ⊢ ∀⁰ atZero matrix := by
  have hi := Classical.choice (IPRAZeroLeft.d_theory _ base_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹]
    Rewriting.emb (∀⁰ atZero matrix)
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]

theorem step_native : nativeTheory ⊢ ∀⁰ ∀⁰ (matrix 🡒 atStep matrix) := by
  have hi := Classical.choice (IPRAZeroLeft.d_theory _ step_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹]
    Rewriting.emb (∀⁰ ∀⁰ (matrix 🡒 atStep matrix))
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]
theorem all_mdp (p q : Semisentenceᵢ language 1)
    (h : nativeTheory ⊢ ∀⁰ (p 🡒 q)) (hp : nativeTheory ⊢ ∀⁰ p) : nativeTheory ⊢ ∀⁰ q := by
  have hd : nativeTheory ⊢ (∀⁰ (p 🡒 q)) 🡒 ((∀⁰ p) 🡒 ∀⁰ q) := by
    apply Nonempty.intro
    apply Theoryᵢ.ofHilbert
    have he := HilbertProofᵢ.allImplyAllOfAllImply (Λ := (𝗜𝗻𝘁¹ : Hilbertᵢ language))
      (Rewriting.emb p) (Rewriting.emb q)
    convert he using 1
    simp [Rewriting.emb]
  exact Entailment.mdp! (Entailment.mdp! hd h) hp

theorem successor_left : nativeTheory ⊢ ∀⁰ ∀⁰ matrix := by
  have hi : nativeTheory ⊢ ∀⁰ (atZero matrix 🡒 ((∀⁰ (matrix 🡒 atStep matrix)) 🡒 ∀⁰ matrix)) := by
    have hh : nativeTheory ⊢ inductionAxiom matrix :=
      IPRANativeAxiomImage.native_axiom (NativeAxiom.induction ⟨1, matrix, matrix_open, rfl⟩)
    simpa [inductionAxiom, inductionBody, allClosure_succ] using hh
  have hstep : nativeTheory ⊢ ∀⁰ ((∀⁰ (matrix 🡒 atStep matrix)) 🡒 ∀⁰ matrix) :=
    all_mdp (atZero matrix) _ hi base_native
  exact all_mdp (∀⁰ (matrix 🡒 atStep matrix)) (∀⁰ matrix) hstep step_native
end DiophantineConsistency.IPRASuccLeft
