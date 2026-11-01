import DiophantineConsistency.IPRAPredReconstruct
set_option autoImplicit false
namespace DiophantineConsistency.IPRAPredSuccessor
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

def predSuccI : Sentenceᵢ language := ∀⁰ (.rel .eq ![.func predCode (fun _ => .func .succ (fun _ => #0)), #0])

theorem pred_succ_closed_context : Δ ⊢[𝗜𝗻𝘁¹] ∀⁰ (.rel .eq ![.func predCode (fun _ => .func .succ (fun _ => #0)), #0]) := by
  have hΔ : Δ⁺ = Δ := by
    simp [Δ, predStepAx, Γ, compAx, projAx, baseAx, stepAx, IPRAEqualityTransGG.ax, reflAx, funAx]
  apply Nonempty.intro
  apply HilbertProofᵢ.geNOverFiniteContext
  rw [hΔ]
  have ho := Classical.choice (pred_succ (&0))
  convert ho using 1
  simp [pred, sc, equal, Rewriting.free, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def]
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i
theorem pred_successor : nativeTheory ⊢ predSuccI := by
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
  have hi := Context.mdp (Context.of (FiniteContext.toDef (Classical.choice pred_succ_closed_context))) (Classical.choice hc)
  change Θ *⊢[𝗜𝗻𝘁¹] (Rewriting.emb predSuccI : Propositionᵢ language)
  apply Nonempty.intro
  convert hi using 1
  simp [predSuccI, Rewriting.emb, Semiformulaᵢ.rew_rel]
  funext i; cases i using Fin.cases with
  | zero => simp [Rew.func, Function.comp_def]
  | succ i => cases i using Fin.cases with
    | zero => rfl
    | succ i => exact Fin.elim0 i

end DiophantineConsistency.IPRAPredSuccessor
