import DiophantineConsistency.IPRAAddRecursion
set_option autoImplicit false
namespace DiophantineConsistency.IPRAZeroLeft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRAPredReconstruct IPRAAddRecursion
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def D : List (Propositionᵢ language) := [funAx addCode (0 : Fin 2), funAx addCode (1 : Fin 2)] ++ Δ
def IH (a : SyntacticTerm language) : Propositionᵢ language := equal (add z a) a
def C (a : SyntacticTerm language) : List (Propositionᵢ language) := IH a :: D
theorem lift_delta {φ : Propositionᵢ language} (h : Δ ⊢[𝗜𝗻𝘁¹] φ) (a : SyntacticTerm language) : C a ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro p hp; simp [C, D, hp]) (Classical.choice h)⟩
theorem trans_new {a b c d : SyntacticTerm language} (h : C a ⊢[𝗜𝗻𝘁¹] equal b c)
    (j : C a ⊢[𝗜𝗻𝘁¹] equal c d) : C a ⊢[𝗜𝗻𝘁¹] equal b d := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context (C a) (by simp [C, D, Δ, Γ]) b c d) h) j
theorem congr_succ {a b c : SyntacticTerm language} (h : C a ⊢[𝗜𝗻𝘁¹] equal b c) : C a ⊢[𝗜𝗻𝘁¹] equal (sc b) (sc c) := by
  have hx : ∀ i : Fin 1, funAx Code.succ i ∈ C a := by
    intro i; cases i using Fin.cases with
    | zero => simp [C, D, Δ, Γ]
    | succ i => exact Fin.elim0 i
  exact function_open_in_context Code.succ (C a) (by simp [C,D,Δ,Γ]) (by simp [C,D,Δ,Γ]) hx _ _ (fun _ => h)
theorem congr_add {a b c d e : SyntacticTerm language}
    (h : C a ⊢[𝗜𝗻𝘁¹] equal b c) (j : C a ⊢[𝗜𝗻𝘁¹] equal d e) :
    C a ⊢[𝗜𝗻𝘁¹] equal (add b d) (add c e) := by
  have hx : ∀ i : Fin 2, funAx addCode i ∈ C a := by
    intro i; cases i using Fin.cases with
    | zero => simp [C,D]
    | succ i => cases i using Fin.cases with
      | zero => simp [C,D]
      | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 2, C a ⊢[𝗜𝗻𝘁¹] equal (![b,d] i) (![c,e] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context addCode (C a) (by simp [C,D,Δ,Γ]) (by simp [C,D,Δ,Γ]) hx _ _ hr

theorem step_open (a : SyntacticTerm language) : C a ⊢[𝗜𝗻𝘁¹] IH (add a one) := by
  have ih : C a ⊢[𝗜𝗻𝘁¹] IH a := ⟨FiniteContext.byAxm (by simp [C])⟩
  have hone := lift_delta (lift_old (add_one_open a)) a
  have hone' := Entailment.mdp! (lift_delta (symm_new _ _) a) hone
  have hrefl := refl_context (C a) (by simp [C,D,Δ,Γ]) z
  exact trans_new (congr_add hrefl hone)
    (trans_new (lift_delta (add_succ_open z a) a)
      (trans_new (congr_succ ih) hone'))
def matrix : Semisentenceᵢ language 1 := .rel .eq ![.func addCode ![zeroTerm 1,#0],#0]
theorem matrix_open : IPRAQuantifierFree.OpenI matrix := by
  simp [matrix, IPRAQuantifierFree.OpenI]

theorem matrix_free : Rewriting.free (Rewriting.emb matrix) = IH (&0) := by
  simp [matrix, IH, add, z, equal, zeroTerm, Rewriting.free, Rewriting.emb,
    Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero => rfl
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem matrix_step_free : Rewriting.free (Rewriting.emb (atStep matrix)) = IH (add (&0) one) := by
  simp [matrix, IH, add, z, one, equal, zeroTerm, stepTerm, atStep, Rewriting.free, Rewriting.emb,
    Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero =>
        simp [Rew.func, Function.comp_def]
        funext k; cases k using Fin.cases with
        | zero => rfl
        | succ k => cases k using Fin.cases with
          | zero => simp [Rew.func, Function.comp_def]; funext l; exact Fin.elim0 l
          | succ k => exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      funext k; cases k using Fin.cases with
      | zero => rfl
      | succ k => cases k using Fin.cases with
        | zero => simp [Rew.func, Function.comp_def]; funext l; exact Fin.elim0 l
        | succ k => exact Fin.elim0 k
    | succ i => exact Fin.elim0 i
theorem step_closed : D ⊢[𝗜𝗻𝘁¹] ∀⁰ (Rewriting.emb matrix 🡒 Rewriting.emb (atStep matrix)) := by
  have hD : D⁺ = D := by
    simp [D, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hD]
  simp only [LogicalConnective.HomClass.map_imply, matrix_free, matrix_step_free]
  exact Classical.choice (FiniteContext.deduct! (step_open (&0)))
theorem d_theory (φ : Propositionᵢ language) (h : D ⊢[𝗜𝗻𝘁¹] φ) :
    (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] φ := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hD : ∀ p ∈ D, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl) | hp
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCode (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCode (1 : Fin 2))))
    · exact IPRAAddRecursion.delta_theory p ⟨FiniteContext.byAxm hp⟩
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀D := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hD
  exact ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice h))) (Classical.choice hc)⟩

theorem base_closed : D ⊢[𝗜𝗻𝘁¹] Rewriting.emb (atZero matrix) := by
  have h : D ⊢[𝗜𝗻𝘁¹] IH z := by
    apply Nonempty.intro
    apply FiniteContext.weakening (Γ := Δ)
    · intro p hp; simp [D, hp]
    · exact Classical.choice (add_zero_open z)
  convert h using 1
  simp [matrix, IH, add, z, equal, zeroTerm, atZero, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ i => exact Fin.elim0 i

theorem base_native : nativeTheory ⊢ atZero matrix := by
  exact d_theory _ base_closed

theorem step_native : nativeTheory ⊢ ∀⁰ (matrix 🡒 atStep matrix) := by
  have hi := Classical.choice (d_theory _ step_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹]
    Rewriting.emb (∀⁰ (matrix 🡒 atStep matrix))
  apply Nonempty.intro
  convert hi using 1
  simp [Rewriting.emb]

theorem zero_left : nativeTheory ⊢ ∀⁰ matrix := by
  have hi : nativeTheory ⊢ inductionAxiom matrix :=
    IPRANativeAxiomImage.native_axiom (NativeAxiom.induction ⟨0, matrix, matrix_open, rfl⟩)
  exact Entailment.mdp! (Entailment.mdp! hi base_native) step_native
end DiophantineConsistency.IPRAZeroLeft
