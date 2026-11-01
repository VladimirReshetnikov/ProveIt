import DiophantineConsistency.IPRAAddRecursion
set_option autoImplicit false
namespace DiophantineConsistency.IPRASubArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRADefiningInstances IPRAPredReconstruct
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def gs : Code 3 := .comp predCode (.cons (.proj 1) (.nil 3))
def subBaseAx : Propositionᵢ language := Rewriting.emb (recursionBaseEquationI (.proj (0 : Fin 1)) gs)
def subStepAx : Propositionᵢ language := Rewriting.emb (recursionStepEquationI (.proj (0 : Fin 1)) gs)
def predBaseAx : Propositionᵢ language := Rewriting.emb (recursionBaseEquationI (.zero 0) (.proj (0 : Fin 2)))
def E : List (Propositionᵢ language) :=
  [compAx subCore swapArgs, compAx predCode (.cons (.proj 1) (.nil 3)), subBaseAx,
   subStepAx, predBaseAx, funAx subCore (0 : Fin 2), funAx subCore (1 : Fin 2)] ++ Δ
def sub (a b : SyntacticTerm language) : SyntacticTerm language := .func subCode ![a,b]
def subcore (a b : SyntacticTerm language) : SyntacticTerm language := .func subCore ![a,b]
theorem lift_delta {φ : Propositionᵢ language} (h : Δ ⊢[𝗜𝗻𝘁¹] φ) : E ⊢[𝗜𝗻𝘁¹] φ := by
  exact ⟨FiniteContext.weakening (by intro p hp; simp [E, hp]) (Classical.choice h)⟩
theorem lift_old {φ : Propositionᵢ language} (h : Γ ⊢[𝗜𝗻𝘁¹] φ) : E ⊢[𝗜𝗻𝘁¹] φ :=
  lift_delta (IPRAPredReconstruct.lift_old h)
theorem trans_new {a b c : SyntacticTerm language} (h : E ⊢[𝗜𝗻𝘁¹] equal a b)
    (j : E ⊢[𝗜𝗻𝘁¹] equal b c) : E ⊢[𝗜𝗻𝘁¹] equal a c := by
  exact Entailment.mdp! (Entailment.mdp! (trans_context E (by simp [E, Δ, Γ]) a b c) h) j
theorem congr_pred {a b : SyntacticTerm language} (h : E ⊢[𝗜𝗻𝘁¹] equal a b) : E ⊢[𝗜𝗻𝘁¹] equal (pred a) (pred b) := by
  have hx : ∀ i : Fin 1, funAx predCode i ∈ E := by
    intro i; cases i using Fin.cases with
    | zero => simp [E, Δ]
    | succ i => exact Fin.elim0 i
  exact function_open_in_context predCode E (by simp [E, Δ, Γ]) (by simp [E, Δ, Γ]) hx _ _ (fun _ => h)
theorem core_congr {a b c d : SyntacticTerm language}
    (h : E ⊢[𝗜𝗻𝘁¹] equal a b) (j : E ⊢[𝗜𝗻𝘁¹] equal c d) :
    E ⊢[𝗜𝗻𝘁¹] equal (subcore a c) (subcore b d) := by
  have hx : ∀ i : Fin 2, funAx subCore i ∈ E := by
    intro i; cases i using Fin.cases with
    | zero => simp [E]
    | succ i => cases i using Fin.cases with
      | zero => simp [E]
      | succ i => exact Fin.elim0 i
  have hr : ∀ i : Fin 2, E ⊢[𝗜𝗻𝘁¹] equal (![a,c] i) (![b,d] i) := by
    intro i; cases i using Fin.cases with
    | zero => exact h
    | succ i => cases i using Fin.cases with
      | zero => exact j
      | succ i => exact Fin.elim0 i
  exact function_open_in_context subCore E (by simp [E, Δ, Γ]) (by simp [E, Δ, Γ]) hx _ _ hr

theorem sub_swap (a b : SyntacticTerm language) : E ⊢[𝗜𝗻𝘁¹] equal (sub a b) (subcore b a) := by
  have h : E ⊢[𝗜𝗻𝘁¹] compAx subCore swapArgs := ⟨FiniteContext.byAxm (by simp [E])⟩
  have hs := composition_instance subCore swapArgs ![a,b] E h
  have hc := core_congr (lift_old (projection21 a b)) (lift_old (projection20 a b))
  apply trans_new ?_ hc
  convert hs using 1
  simp [sub, subcore, subCode, swapArgs, getCode, equal, IPRANativeEquationSpecialize.equal]
  funext i; cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem pred_zero : E ⊢[𝗜𝗻𝘁¹] equal (pred z) z := by
  have h : E ⊢[𝗜𝗻𝘁¹] predBaseAx := ⟨FiniteContext.byAxm (by simp [E])⟩
  have hs := recursion_base_instance (.zero 0) (.proj (0 : Fin 2)) Fin.elim0 E h
  convert hs using 1
  simp [pred, z, predCode, equal, IPRANativeEquationSpecialize.equal]
theorem subcore_base (a : SyntacticTerm language) : E ⊢[𝗜𝗻𝘁¹] equal (subcore z a) a := by
  have h : E ⊢[𝗜𝗻𝘁¹] subBaseAx := ⟨FiniteContext.byAxm (by simp [E])⟩
  have hs := recursion_base_instance (.proj (0 : Fin 1)) gs ![a] E h
  apply trans_new ?_ (lift_old (projection0 a))
  convert hs using 1
  simp [subcore, z, subCore, gs, equal, IPRANativeEquationSpecialize.equal]
  funext i; cases i using Fin.cases with
  | zero => rfl
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem sub_zero (a : SyntacticTerm language) : E ⊢[𝗜𝗻𝘁¹] equal (sub a z) a :=
  trans_new (sub_swap a z) (subcore_base a)

theorem gs_equation (a b c : SyntacticTerm language) :
    E ⊢[𝗜𝗻𝘁¹] equal (.func gs ![a,b,c]) (pred b) := by
  have h : E ⊢[𝗜𝗻𝘁¹] compAx predCode (.cons (.proj 1) (.nil 3)) :=
    ⟨FiniteContext.byAxm (by simp [E])⟩
  have hs := composition_instance predCode (.cons (.proj 1) (.nil 3)) ![a,b,c] E h
  apply trans_new ?_ (congr_pred (lift_old (projection31 a b c)))
  convert hs using 1
  simp [gs, pred, getCode, equal, IPRANativeEquationSpecialize.equal]

theorem subcore_step (a b : SyntacticTerm language) :
    E ⊢[𝗜𝗻𝘁¹] equal (subcore (sc a) b) (pred (subcore a b)) := by
  have h : E ⊢[𝗜𝗻𝘁¹] subStepAx := ⟨FiniteContext.byAxm (by simp [E])⟩
  have hs := recursion_step_instance (.proj (0 : Fin 1)) gs ![a,b] E h
  apply trans_new ?_ (gs_equation a (subcore a b) b)
  convert hs using 1
  simp [subcore, sc, subCore, gs, equal, IPRANativeEquationSpecialize.equal]
  constructor
  · funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i
  · funext i; cases i using Fin.cases with
    | zero => rfl
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => cases i using Fin.cases with
        | zero => rfl
        | succ i => exact Fin.elim0 i

theorem sub_succ (a b : SyntacticTerm language) :
    E ⊢[𝗜𝗻𝘁¹] equal (sub a (sc b)) (pred (sub a b)) := by
  have hsym : E ⊢[𝗜𝗻𝘁¹] equal (subcore b a) (sub a b) :=
    Entailment.mdp! (lift_delta (symm_new _ _)) (sub_swap a b)
  exact trans_new (sub_swap a (sc b)) (trans_new (subcore_step b a) (congr_pred hsym))
theorem e_theory (φ : Propositionᵢ language) (h : E ⊢[𝗜𝗻𝘁¹] φ) :
    (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] φ := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hE : ∀ p ∈ E, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [E, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hp
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionBase _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionStep _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionBase _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix subCore (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix subCore (1 : Fin 2))))
    · exact IPRAAddRecursion.delta_theory p ⟨FiniteContext.byAxm hp⟩
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀E := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hE
  exact ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice h))) (Classical.choice hc)⟩

def subZeroI : Sentenceᵢ language := ∀⁰ (.rel .eq ![.func subCode ![#0, .func (.zero 0) Fin.elim0],#0])
def subSuccI : Sentenceᵢ language := ∀⁰ ∀⁰
  (.rel .eq ![.func subCode ![#1, .func .succ (fun _ => #0)],
    .func predCode (fun _ => .func subCode ![#1,#0])])
theorem sub_zero_closed : E ⊢[𝗜𝗻𝘁¹] ∀⁰ (.rel .eq ![.func subCode ![#0, .func (.zero 0) Fin.elim0],#0]) := by
  have hE : E⁺ = E := by simp [E, subBaseAx, subStepAx, predBaseAx, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hE]
  have ho := Classical.choice (sub_zero (&0))
  convert ho using 1
  simp [sub, z, equal, Rewriting.free, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

theorem sub_zero_native : nativeTheory ⊢ subZeroI := by
  have hi := Classical.choice (e_theory _ sub_zero_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] Rewriting.emb subZeroI
  apply Nonempty.intro
  convert hi using 1
  simp [subZeroI, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
theorem sub_succ_closed : E ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰
  (.rel .eq ![.func subCode ![#1, .func .succ (fun _ => #0)],
    .func predCode (fun _ => .func subCode ![#1,#0])]) := by
  have hE : E⁺ = E := by simp [E, subBaseAx, subStepAx, predBaseAx, Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hE]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hE]
  have ho := Classical.choice (sub_succ (&1) (&0))
  convert ho using 1
  simp [sub, sc, pred, equal, Rewriting.free, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext k; cases k using Fin.cases with
    | zero =>
      change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
      rw [Rew.free_bvar_last, Rew.free_fvar]
    | succ k => cases k using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]
      | succ k => exact Fin.elim0 k
  | succ i => cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      funext k; cases k using Fin.cases with
      | zero =>
        congr 1; funext j; cases j using Fin.cases with
        | zero =>
          change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
          rw [Rew.free_bvar_last, Rew.free_fvar]
        | succ j => cases j using Fin.cases with
          | zero =>
            change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0
            rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
          | succ j => exact Fin.elim0 j
      | succ k => exact Fin.elim0 k
    | succ i => exact Fin.elim0 i
theorem sub_succ_native : nativeTheory ⊢ subSuccI := by
  have hi := Classical.choice (e_theory _ sub_succ_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] Rewriting.emb subSuccI
  apply Nonempty.intro
  convert hi using 1
  simp [subSuccI, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext k; cases k using Fin.cases with
    | zero => rfl
    | succ k => cases k using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]
      | succ k => exact Fin.elim0 k
  | succ i => cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      funext k; cases k using Fin.cases with
      | zero =>
        congr 1; funext j; cases j using Fin.cases with
        | zero => rfl
        | succ j => cases j using Fin.cases with
          | zero => rfl
          | succ j => exact Fin.elim0 j
      | succ k => exact Fin.elim0 k
    | succ i => exact Fin.elim0 i
def predZeroI : Sentenceᵢ language := .rel .eq ![.func predCode (fun _ => .func (.zero 0) Fin.elim0), .func (.zero 0) Fin.elim0]
theorem pred_zero_native : nativeTheory ⊢ predZeroI := by
  have hi := Classical.choice (e_theory _ pred_zero)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] Rewriting.emb predZeroI
  apply Nonempty.intro
  convert hi using 1
  simp [predZeroI, pred, z, equal, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def]; funext j; congr 1; funext k; exact Fin.elim0 k
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
    | succ i => exact Fin.elim0 i
end DiophantineConsistency.IPRASubArithmetic
