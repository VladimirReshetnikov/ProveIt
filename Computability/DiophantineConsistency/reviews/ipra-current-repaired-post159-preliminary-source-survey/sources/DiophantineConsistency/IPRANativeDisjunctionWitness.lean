import DiophantineConsistency.IPRADeepEqualityJoin
/-! Close uniformly instantiated native proofs and construct disjunction stability witnesses from explicit shared-arity child schemas. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeDisjunctionWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRATheoryInstantiation DiophantineConsistency.IPRANativeDeepStability
open DiophantineConsistency.IPRAFoundationZFCStabilityWitness DiophantineConsistency.IPRANativeFormula
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def closeFamily : ∀ (n : ℕ) (φ : Semisentenceᵢ language n),
    (∀ v : Fin n → Term language ℕ, extended nativeTheory ⊢! Rew.embSubsts v ▹ φ) →
    nativeTheory ⊢! ∀⁰* φ
  | 0, φ, h => by
    have hp := h Fin.elim0
    have hr : (Rew.embSubsts (Fin.elim0 : Fin 0 → Term language ℕ)) = (Rew.emb : Rew language Empty 0 ℕ 0) := by
      ext i
      · exact Fin.elim0 i
      · exact Empty.elim i
    rw [hr] at hp
    apply extendedToTheory nativeTheory
    simpa only [allClosure_zero, Rewriting.emb] using hp
  | n+1, φ, h => by
    have hh (v : Fin n → Term language ℕ) : extended nativeTheory ⊢! Rew.embSubsts v ▹ (∀⁰ φ) := by
      apply HilbertProofᵢ.gen
      have hp := h (Fin.cases (&0) (fun i => Rew.shift (v i)))
      have hr : (Rew.free : Rew language ℕ 1 ℕ 0).comp (Rew.embSubsts v).q =
          Rew.embSubsts (Fin.cases (&0) (fun i => Rew.shift (v i))) := by
        ext i
        · cases i using Fin.cases with
          | zero => simp [Rew.comp_app]
          | succ j => simp [Rew.comp_app, Rew.free_bShift_app]
        · exact Empty.elim i
      change extended nativeTheory ⊢! Rew.free ▹ ((Rew.embSubsts v).q ▹ φ)
      rw [← TransitiveRewriting.comp_app, hr]
      exact hp
    have hc := closeFamily n (∀⁰ φ) hh
    simpa only [allClosure_succ] using hc
/-- Both child formulas are represented using the same closed parameter list. -/
def disjunctionWitness (φ ψ : Proposition language) (n : ℕ)
    (a b : Semisentenceᵢ language n) (v : Fin n → Term language ℕ)
    (ha : nativeTheory ⊢! ∀⁰* (a ⋎ ∼a))
    (hb : nativeTheory ⊢! ∀⁰* (∼∼b 🡒 b))
    (hshapeA : (Rew.embSubsts v ▹ a) = native φ)
    (hshapeB : (Rew.embSubsts v ▹ b) = native ψ) :
    StabilityWitness nativeTheory (φ ⋎ ψ) := by
  let body : Semisentenceᵢ language n := ∼∼(a ⋎ b) 🡒 (a ⋎ b)
  have hbody : nativeTheory ⊢! ∀⁰* body := by
    apply closeFamily n body
    intro w
    have hda := instantiateTheory (T := nativeTheory) (a ⋎ ∼a) ha w
    have hsb := instantiateTheory (T := nativeTheory) (∼∼b 🡒 b) hb w
    have hda' : extended nativeTheory ⊢! (Rew.embSubsts w ▹ a) ⋎ ∼(Rew.embSubsts w ▹ a) := by
      simpa only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg] using hda
    have hsb' : extended nativeTheory ⊢! ∼∼(Rew.embSubsts w ▹ b) 🡒 (Rew.embSubsts w ▹ b) := by
      simpa only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using hsb
    have hh := stableOrLeft (Rew.embSubsts w ▹ a) (Rew.embSubsts w ▹ b) hda' hsb'
    simpa only [body, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_neg] using hh
  refine ⟨n,body,v,hbody,?_⟩
  simp only [body, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, hshapeA, hshapeB, native]

def disjunctionWitnessRight (φ ψ : Proposition language) (n : ℕ)
    (a b : Semisentenceᵢ language n) (v : Fin n → Term language ℕ)
    (ha : nativeTheory ⊢! ∀⁰* (∼∼a 🡒 a))
    (hb : nativeTheory ⊢! ∀⁰* (b ⋎ ∼b))
    (hshapeA : (Rew.embSubsts v ▹ a) = native φ)
    (hshapeB : (Rew.embSubsts v ▹ b) = native ψ) :
    StabilityWitness nativeTheory (φ ⋎ ψ) := by
  let body : Semisentenceᵢ language n := ∼∼(a ⋎ b) 🡒 (a ⋎ b)
  have hbody : nativeTheory ⊢! ∀⁰* body := by
    apply closeFamily n body
    intro w
    have hsa := instantiateTheory (T := nativeTheory) (∼∼a 🡒 a) ha w
    have hdb := instantiateTheory (T := nativeTheory) (b ⋎ ∼b) hb w
    have hsa' : extended nativeTheory ⊢! ∼∼(Rew.embSubsts w ▹ a) 🡒 (Rew.embSubsts w ▹ a) := by
      simpa only [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_neg] using hsa
    have hdb' : extended nativeTheory ⊢! (Rew.embSubsts w ▹ b) ⋎ ∼(Rew.embSubsts w ▹ b) := by
      simpa only [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_neg] using hdb
    have hh := stableOrRight (Rew.embSubsts w ▹ a) (Rew.embSubsts w ▹ b) hdb' hsa'
    simpa only [body, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or,
      LogicalConnective.HomClass.map_neg] using hh
  refine ⟨n,body,v,hbody,?_⟩
  simp only [body, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_or,
    LogicalConnective.HomClass.map_neg, hshapeA, hshapeB, native]

end DiophantineConsistency.IPRANativeDisjunctionWitness
