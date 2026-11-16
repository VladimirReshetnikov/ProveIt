import ObjectKernel

/-!
The syntax and axiom layer of the negative-translation plan.

The formula translation, its substitution/weakening laws, QF preservation,
and translation of every classical PRA axiom are proved below.

`ProofTranslationGoal`, `EqualityStabilityGoal`, `NegativeStabilityGoal`,
`RetainedEquivalenceGoal` and `RetainedTransferGoal` are named propositions,
not proofs. In particular this file does NOT implement the complete proof
translator, or add any excluded-middle rule to the target `PRAAx`.
-/

namespace LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax

open Syn
open scoped Fm

def negFormula {n : Nat} (φ : Fm PTm n) : Fm PTm n :=
  φ ⟶ Fm.bot

/-- Atom-preserving negative translation. Its full soundness uses the
    object-arithmetic stability of numerical equality. -/
def negative : {n : Nat} → Fm PTm n → Fm PTm n
  | _, .eq s t => .eq s t
  | _, .bot => .bot
  | _, .and φ ψ => .and (negative φ) (negative ψ)
  | _, .or φ ψ => negFormula (.and (negFormula (negative φ))
      (negFormula (negative ψ)))
  | _, .imp φ ψ => .imp (negative φ) (negative ψ)
  | _, .all φ => .all (negative φ)
  | _, .ex φ => negFormula (.all (negFormula (negative φ)))

/-- Exactly the same nonlogical arithmetic as `PRAAx`, with classical
    excluded middle as a SOURCE axiom schema. -/
inductive ClassicalPRAAx : Theory PTm
  | arith {n : Nat} {φ : Fm PTm n} (h : PRAAx n φ) : ClassicalPRAAx n φ
  | em {n : Nat} (φ : Fm PTm n) : ClassicalPRAAx n (φ ⋎ negFormula φ)

@[simp] theorem negative_subst {n : Nat} (φ : Fm PTm n) :
    ∀ {m : Nat} (σ : Fin n → PTm m),
      negative (φ.subst σ) = (negative φ).subst σ := by
  induction φ <;> intro m σ <;>
    simp_all [negative, negFormula, Fm.subst]

theorem negative_qf {n : Nat} {φ : Fm PTm n} (h : φ.QF) :
    (negative φ).QF := by
  induction φ <;> simp_all [negative, negFormula, Fm.QF]

@[simp] theorem negative_shift {n : Nat} (φ : Fm PTm n) :
    negative φ.shift = (negative φ).shift :=
  negative_subst φ _

def inductionFormula {n : Nat} (φ : Fm PTm (n + 1)) : Fm PTm n :=
  φ.subst (inst PTm.zero) ⟶
    Fm.all (φ ⟶ φ.subst (repl (PTm.succ (var 0)))) ⟶ Fm.all φ

/-- The translated induction instance is the induction instance for the
    translated matrix, with no change of arithmetic strength. -/
theorem negative_inductionFormula {n : Nat} (φ : Fm PTm (n + 1)) :
    negative (inductionFormula φ) = inductionFormula (negative φ) := by
  simp [inductionFormula, negative]

/-- An actual embedded iPRA proof of the translated QF-induction axiom. -/
theorem translatedInductionAxiom {n : Nat} (φ : Fm PTm (n + 1))
    (h : φ.QF) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] negative (inductionFormula φ) := by
  rw [negative_inductionFormula]
  exact Prf.axm (PRAAx.ind (negative φ) (negative_qf h))

/-- Negative excluded middle is proved in the intuitionistic object logic.
    This theorem adds no classical rule to the target theory. -/
theorem translatedExcludedMiddle {n : Nat} (φ : Fm PTm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] negative (φ ⋎ negFormula φ) := by
  exact .impI (.impE (.andE₂ Prf.hyp0) (.andE₁ Prf.hyp0))

/-- All arithmetic axiom translations are actual target derivations. -/
theorem negative_pra_axiom {n : Nat} {φ : Fm PTm n} (h : PRAAx n φ) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] negative φ := by
  cases h with
  | proj i => exact Prf.axm (PRAAx.proj i)
  | comp f gs => exact Prf.axm (PRAAx.comp f gs)
  | precZero f g => exact Prf.axm (PRAAx.precZero f g)
  | precSucc f g => exact Prf.axm (PRAAx.precSucc f g)
  | succNeZero => exact Prf.axm PRAAx.succNeZero
  | succInj => exact Prf.axm PRAAx.succInj
  | ind φ hφ => exact translatedInductionAxiom φ hφ

/-- Completed axiom-translation layer; full derivation translation remains
    the explicitly unproved `ProofTranslationGoal` below. -/
theorem negative_classical_axiom {n : Nat} {φ : Fm PTm n}
    (h : ClassicalPRAAx n φ) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] negative φ := by
  cases h with
  | arith h => exact negative_pra_axiom h
  | em φ => exact translatedExcludedMiddle φ

/-- First formal retained class: QF leaves, and conjunction, implication,
    and universal quantification. Bounded leaves can later be admitted via
    a proved bounded-Booleanization adapter. -/
inductive Retained : {n : Nat} → Fm PTm n → Prop
  | qf {n : Nat} {φ : Fm PTm n} (h : φ.QF) : Retained φ
  | and {n : Nat} {φ ψ : Fm PTm n} (hφ : Retained φ) (hψ : Retained ψ) :
      Retained (φ ⋏ ψ)
  | imp {n : Nat} {φ ψ : Fm PTm n} (hφ : Retained φ) (hψ : Retained ψ) :
      Retained (φ ⟶ ψ)
  | all {n : Nat} {φ : Fm PTm (n + 1)} (hφ : Retained φ) : Retained (Fm.all φ)

/-! The following declarations specify exact completion targets.
    They are definitions of propositions, not theorem declarations. -/

def EqualityStabilityGoal : Prop :=
  ∀ (n : Nat) (s t : PTm n),
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      negFormula (negFormula (s ≐ t)) ⟶ (s ≐ t)

def NegativeStabilityGoal : Prop :=
  ∀ (n : Nat) (φ : Fm PTm n),
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      negFormula (negFormula (negative φ)) ⟶ negative φ

def ProofTranslationGoal : Prop :=
  ∀ (n : Nat) (Γ : List (Fm PTm n)) (φ : Fm PTm n),
    (Γ ⊢[ClassicalPRAAx] φ) →
    (Γ.map negative ⊢[PRAAx] negative φ)

def RetainedEquivalenceGoal : Prop :=
  ∀ (n : Nat) (φ : Fm PTm n), Retained φ →
    (([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff (negative φ) φ)

def RetainedTransferGoal : Prop :=
  ∀ (n : Nat) (Γ : List (Fm PTm n)) (φ : Fm PTm n),
    (∀ ψ ∈ Γ, Retained ψ) → Retained φ →
    ((Γ ⊢[ClassicalPRAAx] φ) ↔ (Γ ⊢[PRAAx] φ))

end LeanProofs.ConciseIPRA.LocalGlobal.NegativeSyntax
