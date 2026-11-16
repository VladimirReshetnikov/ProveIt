import IPRABridge.HilbertLogic
import DiophantineConsistency.IPRAOrderErasureRew
import DiophantineConsistency.IPRAReferenceRew
import DiophantineConsistency.IPRANativeTheory
import DiophantineConsistency.IPRATheoryInstantiation

set_option autoImplicit false

/-! The native order axiom identifies each sentence with the re-embedding of
its equality-only translation. -/

namespace IPRABridge

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open Rewriting
open DiophantineConsistency
open IPRANativeTheory IPRATheoryHilbertBridge IPRATheoryInstantiation
open IPRAOrderErasure IPRAOrderErasureRew IPRAReferenceRew

local notation "L" => PRALanguage.language
local notation "H" => extended nativeTheory

local instance orderRoundtripDecidableEq : PRALanguage.language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

/-- Mapping a native term into the equality-only language and back
preserves its syntax. -/
theorem nativeTermRoundtrip {ξ : Type} {n : ℕ} (t : Semiterm L ξ n) :
    Semiterm.lMap toNative (Semiterm.lMap termsToReference t) = t := by
  induction t with
  | bvar | fvar => rfl
  | func c ts ih =>
    simp only [Semiterm.lMap_func, termsToReference, toNative]
    congr 1
    exact funext ih

private noncomputable def ltIff (ts : Fin 2 → SyntacticTerm L) :
    H ⊢! (.rel Language.ORing.Rel.lt ts) 🡘 embed (erase (.rel Language.ORing.Rel.lt ts)) := by
  let body : Semisentenceᵢ L 2 :=
    .rel Language.ORing.Rel.lt ![.bvar 0, .bvar 1] 🡘
      .rel Language.ORing.Rel.eq
        ![.func PRATheory.ltBitCode (fun i => .bvar i), .func PRALanguage.oneCode Fin.elim0]
  have ax : nativeTheory ⊢! ∀⁰* body := Axiomatized.prfAxm (NativeAxiom.basic .orderDefinition)
  have h := instantiateTheory body ax ts
  have hVars : (fun i => Rew.embSubsts ts (![.bvar 0, .bvar 1] i)) = ts := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Rew.embSubsts_bvar _ _
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      exact Rew.embSubsts_bvar _ _
  have hBit (i : Fin 2) :
      Rew.embSubsts ts
        (![.func PRATheory.ltBitCode (fun j => .bvar j), .func PRALanguage.oneCode Fin.elim0] i) =
          ![.func PRATheory.ltBitCode ts, .func PRALanguage.oneCode Fin.elim0] i := by
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Matrix.cons_val_zero, Rew.func', Rew.embSubsts_bvar]
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Rew.func']
      congr 1
      exact funext isEmptyElim
  have hImage : embed (erase (.rel Language.ORing.Rel.lt ts)) =
      .rel Language.ORing.Rel.eq
        ![.func PRATheory.ltBitCode ts, .func PRALanguage.oneCode Fin.elim0] := by
    simp only [embed, erase]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Matrix.cons_val_zero, Semiterm.lMap_func, toNative]
      congr 1
      exact funext (fun j => nativeTermRoundtrip (ts j))
    · refine Fin.cases ?_ (fun j => Fin.elim0 j) j
      simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Semiterm.lMap_func, toNative]
      congr 1
      exact funext isEmptyElim
  simpa only [body, LogicalConnective.HomClass.map_iff, Semiformulaᵢ.rew_rel, hVars, hBit, hImage] using h

/-- Order erasure preserves open native formulas under their existing free variables. -/
noncomputable def nativeOrderRoundtripOpen : (φ : Propositionᵢ L) → H ⊢! φ 🡘 embed (erase φ)
  | .falsum => Entailment.E_Id
  | .rel .eq ts => by
    simp only [erase, embed, nativeTermRoundtrip]
    exact Entailment.E_Id
  | .rel .lt ts => ltIff ts
  | .and φ ψ => Entailment.EKK_of_E_of_E (nativeOrderRoundtripOpen φ) (nativeOrderRoundtripOpen ψ)
  | .or φ ψ => Entailment.EAA_of_E_of_E (nativeOrderRoundtripOpen φ) (nativeOrderRoundtripOpen ψ)
  | .imp φ ψ => Entailment.ECC_of_E_of_E (nativeOrderRoundtripOpen φ) (nativeOrderRoundtripOpen ψ)
  | .all φ => by
    apply HilbertProofᵢ.allIffAllOfIff
    simpa only [erase_free, embed_free] using nativeOrderRoundtripOpen (Rewriting.free φ)
  | .exs φ => by
    have h : H ⊢! Rewriting.free φ 🡘 Rewriting.free (embed (erase φ)) := by
      simpa only [erase_free, embed_free] using nativeOrderRoundtripOpen (Rewriting.free φ)
    exact Entailment.E_intro (existsImpOfFreeImp (Entailment.K_left h)) (existsImpOfFreeImp (Entailment.K_right h))
  termination_by φ => φ.complexity

/-- Erasing order and embedding the result preserves a native sentence up to
a biconditional provable in native iPRA. -/
theorem nativeOrderRoundtrip (φ : Sentenceᵢ L) : nativeTheory ⊢ φ 🡘 embed (erase φ) := by
  apply Nonempty.intro
  apply extendedToTheory nativeTheory
  simpa only [LogicalConnective.HomClass.map_iff, erase_emb, embed_emb] using
    nativeOrderRoundtripOpen (Rewriting.emb φ)

end IPRABridge
