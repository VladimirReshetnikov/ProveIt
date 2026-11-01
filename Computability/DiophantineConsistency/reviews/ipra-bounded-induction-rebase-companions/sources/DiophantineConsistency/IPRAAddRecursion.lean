import DiophantineConsistency.IPRAPredReconstruct
set_option autoImplicit false
namespace DiophantineConsistency.IPRAAddRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRAPredReconstruct
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

theorem add_zero_open (a : SyntacticTerm language) : Δ ⊢[𝗜𝗻𝘁¹] equal (add a z) a :=
  trans_new (lift_old (swap_equation a z)) (lift_old (core_base a))

theorem add_succ_open (a b : SyntacticTerm language) :
    Δ ⊢[𝗜𝗻𝘁¹] equal (add a (sc b)) (sc (add a b)) := by
  have h := lift_old (swap_equation a b)
  have he := Entailment.mdp! (symm_new _ _) h
  exact trans_new (lift_old (swap_equation a (sc b)))
    (trans_new (lift_old (core_step b a)) (congr_succ he))
theorem delta_theory (φ : Propositionᵢ language) (h : Δ ⊢[𝗜𝗻𝘁¹] φ) :
    (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] φ := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : ∀ p ∈ Γ, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionBase _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionStep _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution IPRAEqualityTransGG.matrix))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCore (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix addCore (1 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix Code.succ (0 : Fin 1))))
  have hδ : ∀ p ∈ Δ, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [Δ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with (rfl | rfl | rfl) | hp
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionStep _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality
        (EqualityAxiomI.substitution (funMatrix predCode (0 : Fin 1))))
    · exact IPRAEqualitySymmetryGG.symmetry_native
    · exact hax p hp
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀Δ := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hδ
  exact ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice h))) (Classical.choice hc)⟩

def addZeroI : Sentenceᵢ language := ∀⁰ (.rel .eq ![.func addCode ![#0, .func (.zero 0) Fin.elim0],#0])
def addSuccI : Sentenceᵢ language := ∀⁰ ∀⁰
  (.rel .eq ![.func addCode ![#1, .func .succ (fun _ => #0)],
    .func .succ (fun _ => .func addCode ![#1,#0])])

theorem add_zero_closed : Δ ⊢[𝗜𝗻𝘁¹] ∀⁰ (.rel .eq ![.func addCode ![#0, .func (.zero 0) Fin.elim0],#0]) := by
  have hΔ : Δ⁺ = Δ := by simp [Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΔ]
  have ho := Classical.choice (add_zero_open (&0))
  convert ho using 1
  simp [add, z, equal, Rewriting.free, Semiformulaᵢ.rew_rel]
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

theorem add_zero_native : nativeTheory ⊢ addZeroI := by
  have hi := Classical.choice (delta_theory _ add_zero_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] Rewriting.emb addZeroI
  apply Nonempty.intro
  convert hi using 1
  simp [addZeroI, Rewriting.emb, Semiformulaᵢ.rew_rel]
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
theorem add_succ_closed : Δ ⊢[𝗜𝗻𝘁¹] ∀⁰ ∀⁰
  (.rel .eq ![.func addCode ![#1, .func .succ (fun _ => #0)],
    .func .succ (fun _ => .func addCode ![#1,#0])]) := by
  have hΔ : Δ⁺ = Δ := by simp [Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΔ]
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΔ]
  have ho := Classical.choice (add_succ_open (&1) (&0))
  convert ho using 1
  simp [add, sc, equal, Rewriting.free, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def]
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
theorem add_succ_native : nativeTheory ⊢ addSuccI := by
  have hi := Classical.choice (delta_theory _ add_succ_closed)
  change (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] Rewriting.emb addSuccI
  apply Nonempty.intro
  convert hi using 1
  simp [addSuccI, Rewriting.emb, Semiformulaᵢ.rew_rel]
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



end DiophantineConsistency.IPRAAddRecursion
