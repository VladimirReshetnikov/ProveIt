import DiophantineConsistency.IPRAOrderErasureHilbert
import DiophantineConsistency.IPRANativeTheory

/-! Conditional native-to-reference derivation transport. The premise that
every native axiom erases to a reference-theory theorem is explicit and is not
discharged here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAOrderErasureTheoryTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAOrderErasureRew IPRAOrderErasureHilbert
open PRAFiniteFunctionCodes IPRAEqualityOnlyReference

local instance : IPRAEqualityOnlyReference.language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (EqualityRel k); infer_instance

theorem erase_conj : (xs : List (Propositionᵢ PRALanguage.language)) →
    erase (⋀xs) = ⋀(xs.map erase)
  | [] => rfl
  | [x] => rfl
  | x :: y :: xs => by
    simp only [List.conj₂, List.map, erase]
    rw [erase_conj (y :: xs)]
    rfl

def conjProof :
    (xs : List (Propositionᵢ IPRAEqualityOnlyReference.language)) →
      (∀ x ∈ xs, (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! x) →
      (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⋀xs
  | [], _ => by simpa using
      (Entailment.verum : (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⊤)
  | [x], h => by simpa using h x (by simp)
  | x :: y :: xs, h => by
    have hx := h x (by simp)
    have hrest := conjProof (y :: xs) (by intro z hz; exact h z (by simp [hz]))
    simpa only [List.conj₂] using Entailment.K_intro hx hrest

def transfer {φ : Sentenceᵢ PRALanguage.language}
    (h : ∀ σ, σ ∈ IPRANativeTheory.nativeTheory.theory → referenceTheory ⊢ erase σ)
    (p : IPRANativeTheory.nativeTheory ⊢! φ) : referenceTheory ⊢! erase φ := by
  rcases p with ⟨xs, hs, hp⟩
  have hall : (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⋀(xs.map erase) := by
    apply conjProof
    intro y hy
    have hex := List.mem_map.mp hy
    let x := Classical.choose hex
    have hx := (Classical.choose_spec hex).1
    have hyx := (Classical.choose_spec hex).2
    rw [← hyx]
    have he : x ∈ Rewriting.emb '' IPRANativeTheory.nativeTheory.theory := hs x hx
    let σ := Classical.choose he
    have hσ := (Classical.choose_spec he).1
    have heq := (Classical.choose_spec he).2
    change (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! erase x
    rw [← heq, erase_emb]
    exact Classical.choice (h σ hσ)
  have hlogic := eraseHilbert (Entailment.FiniteContext.toDef hp)
  have hlogic' : (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language) ⊢!
      (⋀(xs.map erase) 🡒 Rewriting.emb (erase φ)) := by
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (Semiformulaᵢ.imp (⋀(xs.map erase)) (Rewriting.emb (erase φ)))
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ IPRAEqualityOnlyReference.language)
      (erase (⋀xs 🡒 Rewriting.emb φ)) at hlogic
    simpa only [erase, erase_conj, erase_emb] using hlogic
  change (Rewriting.emb '' referenceTheory.theory) *⊢[𝗜𝗻𝘁¹]! Rewriting.emb (erase φ)
  exact Entailment.Context.mdp (Entailment.Context.of hlogic') hall

theorem transfer_provable {φ : Sentenceᵢ PRALanguage.language}
    (h : ∀ σ, σ ∈ IPRANativeTheory.nativeTheory.theory → referenceTheory ⊢ erase σ)
    (p : IPRANativeTheory.nativeTheory ⊢ φ) : referenceTheory ⊢ erase φ := by
  rcases p with ⟨p⟩
  exact ⟨transfer h p⟩

end DiophantineConsistency.IPRAOrderErasureTheoryTransfer
