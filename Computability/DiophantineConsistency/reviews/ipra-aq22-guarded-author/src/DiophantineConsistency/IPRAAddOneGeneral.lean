import DiophantineConsistency.IPRASuccessorInduction
import DiophantineConsistency.IPRAAddOneDirect
/-! Direct add-one in an arbitrary theory with the native defining and equality schemas; no induction premise. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAddOneGeneral
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAAddOneDirect DiophantineConsistency.IPRAFunctionCongruenceOpen
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
theorem addOne {T : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)}
    (hdef : ∀ σ, DefiningEquationI σ → T ⊢ σ)
    (heq : ∀ σ, EqualityAxiomI σ → T ⊢ σ) : T ⊢ addOneI := by
  let Δ : Set (Propositionᵢ language) := Rewriting.emb '' T.theory
  have hax : ∀ p ∈ Γ, Δ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hdef _ (DefiningEquationI.composition _ _)
    · exact hdef _ (DefiningEquationI.composition _ _)
    · exact hdef _ (DefiningEquationI.composition _ _)
    · exact hdef _ (DefiningEquationI.projection _)
    · exact hdef _ (DefiningEquationI.projection _)
    · exact hdef _ (DefiningEquationI.projection _)
    · exact hdef _ (DefiningEquationI.projection _)
    · exact hdef _ (DefiningEquationI.recursionBase _ _)
    · exact hdef _ (DefiningEquationI.recursionStep _ _)
    · exact heq _ (EqualityAxiomI.substitution DiophantineConsistency.IPRAEqualityTransGG.matrix)
    · exact heq _ EqualityAxiomI.refl
    · exact heq _ (EqualityAxiomI.substitution (funMatrix addCore (0 : Fin 2)))
    · exact heq _ (EqualityAxiomI.substitution (funMatrix addCore (1 : Fin 2)))
    · exact heq _ (EqualityAxiomI.substitution (funMatrix Code.succ (0 : Fin 1)))
  have hc : Δ *⊢[𝗜𝗻𝘁¹] ⋀Γ := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hax
  have hi := Context.mdp (Context.of (FiniteContext.toDef (Classical.choice add_one_closed_context))) (Classical.choice hc)
  change Δ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb addOneI : Propositionᵢ language)
  apply Nonempty.intro
  convert hi using 1
  simp [addOneI, Rewriting.emb, stepTerm, applyCode, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero =>
    simp [Rew.func, Function.comp_def]
    funext j; cases j using Fin.cases with
    | zero => rfl
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  | succ i => cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ i => exact Fin.elim0 i

end DiophantineConsistency.IPRAAddOneGeneral
