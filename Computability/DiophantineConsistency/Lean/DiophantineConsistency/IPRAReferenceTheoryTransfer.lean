import DiophantineConsistency.IPRAReferenceHilbert
import DiophantineConsistency.IPRANativeTheory

/-! Conditional reference-to-native theory-proof transport. The reference
axiom-image premise is explicit; no theory equivalence or equation endpoint is
asserted here. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReferenceTheoryTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open IPRAOrderErasure IPRAReferenceRew IPRAReferenceHilbert
open PRAFiniteFunctionCodes

local instance : PRALanguage.language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem embed_conj : (xs : List (Propositionᵢ IPRAEqualityOnlyReference.language)) →
    embed (⋀xs) = ⋀(xs.map embed)
  | [] => rfl
  | [x] => rfl
  | x :: y :: xs => by
    simp only [List.conj₂, List.map, embed]
    rw [embed_conj (y :: xs)]
    rfl

def conjProof :
    (xs : List (Propositionᵢ PRALanguage.language)) →
      (∀ x ∈ xs, (Rewriting.emb '' IPRANativeTheory.nativeTheory.theory) *⊢[𝗜𝗻𝘁¹]! x) →
      (Rewriting.emb '' IPRANativeTheory.nativeTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⋀xs
  | [], _ => by simpa using
      (Entailment.verum : (Rewriting.emb '' IPRANativeTheory.nativeTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⊤)
  | [x], h => by simpa using h x (by simp)
  | x :: y :: xs, h => by
    have hx := h x (by simp)
    have hrest := conjProof (y :: xs) (by intro z hz; exact h z (by simp [hz]))
    simpa only [List.conj₂] using Entailment.K_intro hx hrest

def transfer {φ : Sentenceᵢ IPRAEqualityOnlyReference.language}
    (h : ∀ σ, σ ∈ IPRAEqualityOnlyReference.referenceTheory.theory →
      IPRANativeTheory.nativeTheory ⊢ embed σ)
    (p : IPRAEqualityOnlyReference.referenceTheory ⊢! φ) :
    IPRANativeTheory.nativeTheory ⊢! embed φ := by
  rcases p with ⟨xs, hs, hp⟩
  have hall : (Rewriting.emb '' IPRANativeTheory.nativeTheory.theory) *⊢[𝗜𝗻𝘁¹]! ⋀(xs.map embed) := by
    apply conjProof
    intro y hy
    have hex := List.mem_map.mp hy
    let x := Classical.choose hex
    have hx := (Classical.choose_spec hex).1
    have hyx := (Classical.choose_spec hex).2
    rw [← hyx]
    have he : x ∈ Rewriting.emb '' IPRAEqualityOnlyReference.referenceTheory.theory := hs x hx
    let σ := Classical.choose he
    have hσ := (Classical.choose_spec he).1
    have heq := (Classical.choose_spec he).2
    change (Rewriting.emb '' IPRANativeTheory.nativeTheory.theory) *⊢[𝗜𝗻𝘁¹]! embed x
    rw [← heq, embed_emb]
    exact Classical.choice (h σ hσ)
  have hlogic := embedHilbert (Entailment.FiniteContext.toDef hp)
  have hlogic' : (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language) ⊢!
      (⋀(xs.map embed) 🡒 Rewriting.emb (embed φ)) := by
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (Semiformulaᵢ.imp (⋀(xs.map embed)) (Rewriting.emb (embed φ)))
    change HilbertProofᵢ (𝗜𝗻𝘁¹ : Hilbertᵢ PRALanguage.language)
      (embed (⋀xs 🡒 Rewriting.emb φ)) at hlogic
    simpa only [embed, embed_conj, embed_emb] using hlogic
  change (Rewriting.emb '' IPRANativeTheory.nativeTheory.theory) *⊢[𝗜𝗻𝘁¹]!
    Rewriting.emb (embed φ)
  exact Entailment.Context.mdp (Entailment.Context.of hlogic') hall

theorem transfer_provable {φ : Sentenceᵢ IPRAEqualityOnlyReference.language}
    (h : ∀ σ, σ ∈ IPRAEqualityOnlyReference.referenceTheory.theory →
      IPRANativeTheory.nativeTheory ⊢ embed σ)
    (p : IPRAEqualityOnlyReference.referenceTheory ⊢ φ) :
    IPRANativeTheory.nativeTheory ⊢ embed φ := by
  rcases p with ⟨p⟩
  exact ⟨transfer h p⟩

end DiophantineConsistency.IPRAReferenceTheoryTransfer
