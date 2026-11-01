import DiophantineConsistency.IPRASuccessorInductionConverse
/-! Same-language derivability equivalence when only the induction step changes. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASuccessorTheoryEquivalence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage IPRANativeTheory IPRAQuantifierFree IPRANativeInduction IPRASuccessorInduction IPRASuccessorInductionConverse
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
inductive SuccAxiom : Sentenceᵢ language → Prop
  | equality {σ} : EqualityAxiomI σ → SuccAxiom σ
  | defining {σ} : DefiningEquationI σ → SuccAxiom σ
  | basic {σ} : BasicAxiomI σ → SuccAxiom σ
  | induction {n} (φ : Semisentenceᵢ language (n+1)) : OpenI φ → SuccAxiom (succInductionAxiom φ)
def successorTheory : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language) := ⟨{σ | SuccAxiom σ}⟩
theorem native_to_successor_axiom {σ} (h : NativeAxiom σ) : successorTheory ⊢ σ := by
 cases h with
 | equality h => exact ⟨Axiomatized.prfAxm (SuccAxiom.equality h)⟩
 | defining h => exact ⟨Axiomatized.prfAxm (SuccAxiom.defining h)⟩
 | basic h => exact ⟨Axiomatized.prfAxm (SuccAxiom.basic h)⟩
 | induction h =>
   rcases h with ⟨n, φ, ho, rfl⟩
   exact ⟨plusInductionFromSucc (fun _ h => Axiomatized.prfAxm (SuccAxiom.defining h))
     (fun _ h => Axiomatized.prfAxm (SuccAxiom.equality h)) φ
     (Axiomatized.prfAxm (SuccAxiom.induction φ ho))⟩
theorem successor_to_native_axiom {σ} (h : SuccAxiom σ) : nativeTheory ⊢ σ := by
 cases h with
 | equality h => exact ⟨Axiomatized.prfAxm (NativeAxiom.equality h)⟩
 | defining h => exact ⟨Axiomatized.prfAxm (NativeAxiom.defining h)⟩
 | basic h => exact ⟨Axiomatized.prfAxm (NativeAxiom.basic h)⟩
 | induction φ ho => exact ⟨successorInduction φ ho⟩
def conjProof {U : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)} :
    (xs : List (Propositionᵢ language)) → (∀ x ∈ xs, (Rewriting.emb '' U.theory) *⊢[𝗜𝗻𝘁¹]! x) →
      (Rewriting.emb '' U.theory) *⊢[𝗜𝗻𝘁¹]! ⋀xs
  | [], _ => by simpa using (Entailment.verum : (Rewriting.emb '' U.theory) *⊢[𝗜𝗻𝘁¹]! ⊤)
  | [x], h => by simpa using h x (by simp)
  | x :: y :: xs, h => by
    have hx := h x (by simp)
    have hrest := conjProof (y :: xs) (by intro z hz; exact h z (by simp [hz]))
    simpa only [List.conj₂] using Entailment.K_intro hx hrest

def transfer {T U : Theoryᵢ language (𝗜𝗻𝘁¹ : Hilbertᵢ language)} {φ : Sentenceᵢ language}
    (h : ∀ σ, σ ∈ T.theory → U ⊢ σ) (p : T ⊢! φ) : U ⊢! φ := by
  rcases p with ⟨xs, hs, hp⟩
  have hall : (Rewriting.emb '' U.theory) *⊢[𝗜𝗻𝘁¹]! ⋀xs := by
    apply conjProof xs
    intro x hx
    have he : x ∈ Rewriting.emb '' T.theory := hs x hx
    let σ := Classical.choose he
    have hσ := (Classical.choose_spec he).1
    have heq := (Classical.choose_spec he).2
    rw [← heq]
    exact Classical.choice (h σ hσ)
  change (Rewriting.emb '' U.theory) *⊢[𝗜𝗻𝘁¹]! Rewriting.emb φ
  exact Entailment.Context.mdp (Entailment.Context.of (Entailment.FiniteContext.toDef hp)) hall

theorem same_derivability (φ : Sentenceᵢ language) : nativeTheory ⊢ φ ↔ successorTheory ⊢ φ := by
  constructor
  · rintro ⟨p⟩
    exact ⟨transfer (fun _ h => native_to_successor_axiom h) p⟩
  · rintro ⟨p⟩
    exact ⟨transfer (fun _ h => successor_to_native_axiom h) p⟩
end DiophantineConsistency.IPRASuccessorTheoryEquivalence
