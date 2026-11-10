import DiophantineConsistency.Sign14Positive74ObjectMulZeroContext
import DiophantineConsistency.IPRANativeAxiomImage

/-! SOURCE ONLY: discharge displayed mul-zero context in nativeTheory. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectMulZeroNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open Rewriting HilbertProofᵢ
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory IPRATheoryHilbertBridge
open IPRAFunctionCongruenceOpen IPRAAddOneDirect Sign14Positive74ObjectMulZeroContext
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem contextNative (φ : Propositionᵢ language) (h : Δ ⊢[𝗜𝗻𝘁¹] φ) :
    (Rewriting.emb '' nativeTheory.theory : Set (Propositionᵢ language)) *⊢[𝗜𝗻𝘁¹] φ := by
  let Θ : Set (Propositionᵢ language) := Rewriting.emb '' nativeTheory.theory
  have hax : ∀ p ∈ Δ, Θ *⊢[𝗜𝗻𝘁¹] p := by
    intro p hp
    simp only [Δ, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.composition _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.projection _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.recursionBase _ _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.defining (DefiningEquationI.zero _))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution IPRAEqualityTransGG.matrix))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality EqualityAxiomI.refl)
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix mulCore (0 : Fin 2))))
    · exact IPRANativeAxiomImage.native_axiom (NativeAxiom.equality (EqualityAxiomI.substitution (funMatrix mulCore (1 : Fin 2))))
  have hc : Θ *⊢[𝗜𝗻𝘁¹] ⋀Δ := by
    apply Conj₂!_iff_forall_provable.mpr
    exact hax
  exact ⟨Context.mdp (Context.of (FiniteContext.toDef (Classical.choice h))) (Classical.choice hc)⟩

def mulZeroOpen (a : SyntacticTerm language) : extended nativeTheory ⊢! equal (mult a mz) mz := by
  have hctx := Classical.choice (contextNative _ (mul_zero a))
  have hp : extended nativeTheory ⊢! ⋀hctx.ctx 🡒 equal (mult a mz) mz :=
    HilbertProofᵢ.ofLE (le_extended nativeTheory) hctx.prf
  have hc : extended nativeTheory ⊢! ⋀hctx.ctx :=
    Entailment.Conj₂_intro hctx.ctx (fun ψ hψ => HilbertProofᵢ.eaxm (Or.inr (hctx.subset ψ hψ)))
  exact hp ⨀ hc
end DiophantineConsistency.Sign14Positive74ObjectMulZeroNative
#print axioms DiophantineConsistency.Sign14Positive74ObjectMulZeroNative.contextNative
#print axioms DiophantineConsistency.Sign14Positive74ObjectMulZeroNative.mulZeroOpen
