import IPRABridge.HilbertLogic
import IPRABridge.CodeNormalization
import IPRABridge.SyntaxNormalization

/-! In Foundation's equality-only theory, normalization of primitive-recursive
codes preserves every term and formula up to object-theory provable equality
or biconditional. -/

set_option autoImplicit false
noncomputable section

namespace IPRABridge

open LO LO.FirstOrder LO.Entailment LO.Entailment.FiniteContext
open scoped LO.FirstOrder
open DiophantineConsistency
open IPRAEqualityOnlyReference
open IPRAReferenceEqualityTools (eqAt)
open IPRATheoryHilbertBridge (extended extendedToTheory)
open ConciseToFoundationLogic (atEnv eqReflAt replaceEnv)

local instance normalizedReferenceLanguageDecidableEq : language.DecidableEq where
  func k := by
    change DecidableEq (PRAFiniteFunctionCodes.Code k)
    infer_instance
  rel k := by
    change DecidableEq (EqualityRel k)
    infer_instance

local notation "H" => extended referenceTheory

/-- The normalization of a reference-language term is provably equal to it. -/
def referenceTermNormalization (t : Term language ℕ) :
    H ⊢! eqAt t (normalizeTerm t) := by
  induction t with
  | bvar i => exact Fin.elim0 i
  | fvar x => exact eqReflAt (.fvar x)
  | func c ts ih =>
    change H ⊢! eqAt (.func c ts) (.func (normalizeCode c) (fun i => normalizeTerm (ts i)))
    exact emptyPrf (referenceEqTrans ⟨of (normalizeCode_eq c ts)⟩
      (referenceFuncCongr (normalizeCode c) ts (fun i => normalizeTerm (ts i))
        (fun i => ⟨of (ih i)⟩))).some

private def atomCongr (ts us : Fin 2 → Term language ℕ)
    (h : ∀ i, H ⊢! eqAt (ts i) (us i)) :
    H ⊢! (Semiformulaᵢ.rel EqualityRel.eq ts) 🡘 (Semiformulaᵢ.rel EqualityRel.eq us) := by
  let p : Semisentenceᵢ language 2 := .rel EqualityRel.eq (fun i => .bvar i)
  have hEnv (v : Fin 2 → Term language ℕ) :
      atEnv v p = .rel EqualityRel.eq v := by
    simp only [atEnv, p, Semiformulaᵢ.rew_rel, Rew.embSubsts_bvar]
  apply Entailment.E_intro
  · apply deduct'
    have hts : [Semiformulaᵢ.rel EqualityRel.eq ts] ⊢[H] atEnv ts p := by
      rw [hEnv]
      exact ⟨byAxm₀⟩
    simpa only [hEnv] using
      (replaceEnv p ts us (fun i => ⟨of (h i)⟩) hts).some
  · apply deduct'
    have hus : [Semiformulaᵢ.rel EqualityRel.eq us] ⊢[H] atEnv us p := by
      rw [hEnv]
      exact ⟨byAxm₀⟩
    simpa only [hEnv] using
      (replaceEnv p us ts (fun i => referenceEqSymm ⟨of (h i)⟩) hus).some

/-- Normalization preserves provability even when the formula contains free
variables. Under a binder the proof is reopened with a fresh variable. -/
def referenceNormalizationOpen : (φ : Propositionᵢ language) →
    H ⊢! φ 🡘 normalizeFormula φ
  | .falsum => Entailment.E_Id
  | .rel .eq ts => atomCongr ts _ (fun i => referenceTermNormalization (ts i))
  | .and φ ψ => Entailment.EKK_of_E_of_E (referenceNormalizationOpen φ) (referenceNormalizationOpen ψ)
  | .or φ ψ => Entailment.EAA_of_E_of_E (referenceNormalizationOpen φ) (referenceNormalizationOpen ψ)
  | .imp φ ψ => Entailment.ECC_of_E_of_E (referenceNormalizationOpen φ) (referenceNormalizationOpen ψ)
  | .all φ => by
    apply HilbertProofᵢ.allIffAllOfIff
    simpa only [normalizeFormula_free] using referenceNormalizationOpen (Rewriting.free φ)
  | .exs φ => by
    have h : H ⊢! Rewriting.free φ 🡘 Rewriting.free (normalizeFormula φ) := by
      simpa only [normalizeFormula_free] using referenceNormalizationOpen (Rewriting.free φ)
    exact Entailment.E_intro (existsImpOfFreeImp (Entailment.K_left h))
      (existsImpOfFreeImp (Entailment.K_right h))
  termination_by φ => φ.complexity

/-- A reference sentence and its normalized form are provably equivalent. -/
theorem referenceNormalization (φ : Sentenceᵢ language) : referenceTheory ⊢ φ 🡘 normalizeFormula φ := by
  apply Nonempty.intro
  apply extendedToTheory referenceTheory
  simpa only [LogicalConnective.HomClass.map_iff, normalizeFormula_emb] using
    referenceNormalizationOpen (Rewriting.emb φ)

end IPRABridge
