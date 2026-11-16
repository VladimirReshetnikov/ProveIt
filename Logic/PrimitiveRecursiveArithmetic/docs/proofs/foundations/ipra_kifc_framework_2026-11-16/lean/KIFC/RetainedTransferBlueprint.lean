import KIFC.BooleanBlueprint

/-!
# Completion blueprint for classical-to-intuitionistic retained transfer

This source-oriented blueprint follows the atom-preserving negative translation already present in
ProveIt's `ipra_local_global/lean/NegativeSyntax.lean`.  It records the exact missing theorems and
proof decomposition.  `sorry` marks the precisely delimited implementation work; no theorem containing
those placeholders is claimed kernel-checked by this artifact.  In repository
integration, reuse the upstream syntax and axiom-translation declarations rather
than maintaining the duplicate definitions below.
-/

namespace LeanProofs.KIFC.RetainedTransfer

open Syn
open scoped Fm

/-- Object negation. -/
def negFormula {n : Nat} (A : Fm PTm n) : Fm PTm n :=
  A ⟶ Fm.bot

/-- Atom-preserving Gödel-Gentzen translation. -/
def negative : {n : Nat} → Fm PTm n → Fm PTm n
  | _, .eq s t => .eq s t
  | _, .bot => .bot
  | _, .and A B => .and (negative A) (negative B)
  | _, .or A B => negFormula (.and (negFormula (negative A))
      (negFormula (negative B)))
  | _, .imp A B => .imp (negative A) (negative B)
  | _, .all A => .all (negative A)
  | _, .ex A => negFormula (.all (negFormula (negative A)))

/-- Classical source theory: same arithmetic plus EM. -/
inductive ClassicalPRAAx : Theory PTm
  | arith {n : Nat} {A : Fm PTm n} (h : PRAAx n A) : ClassicalPRAAx n A
  | em {n : Nat} (A : Fm PTm n) : ClassicalPRAAx n (A ⋎ negFormula A)

@[simp] theorem negative_subst {n : Nat} (A : Fm PTm n) :
    ∀ {m : Nat} (σ : Fin n → PTm m),
      negative (A.subst σ) = (negative A).subst σ := by
  induction A <;> intro m σ <;>
    simp_all [negative, negFormula, Fm.subst]

/-- Numerical equality is stable because a reflected PR equality Boolean
proves decidability.  Dependency: `KIFC Boolean reflection compiler`. -/
theorem equality_stable_target {n : Nat} (s t : PTm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      negFormula (negFormula (s ≐ t)) ⟶ (s ≐ t) := by
  sorry

/-- All translated formulas are stable.  Structural proof described in the
paper; disjunction/existential translations are negations. -/
theorem negative_stable_target {n : Nat} (A : Fm PTm n) :
    ([] : List (Fm PTm n)) ⊢[PRAAx]
      negFormula (negFormula (negative A)) ⟶ negative A := by
  induction A with
  | eq s t => exact equality_stable_target s t
  | bot => sorry
  | and A B ihA ihB => sorry
  | or A B ihA ihB => sorry
  | imp A B ihA ihB => sorry
  | all A ih => sorry
  | ex A ih => sorry

/-- Arithmetic axioms and EM translate; the repository blueprint already
contains source-complete proofs of these cases. -/
theorem translate_axiom_target {n : Nat} {A : Fm PTm n}
    (h : ClassicalPRAAx n A) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] negative A := by
  sorry

/-- Main proof-translation theorem.  The nontrivial `orE` and `exE` cases
first derive double negation of the translated conclusion and then apply
`negative_stable_target`. -/
theorem translate_prf_target {n : Nat}
    {Γ : List (Fm PTm n)} {A : Fm PTm n}
    (h : Γ ⊢[ClassicalPRAAx] A) :
    Γ.map negative ⊢[PRAAx] negative A := by
  induction h with
  | hyp hmem => exact Prf.hyp (List.mem_map_of_mem hmem)
  | ax h σ =>
      have ha := (translate_axiom_target h).subst σ
      simpa [negative_subst] using ha
  | botE A h ih => exact Prf.botE _ ih
  | andI hA hB ihA ihB => exact Prf.andI ihA ihB
  | andE₁ h ih => exact Prf.andE₁ ih
  | andE₂ h ih => exact Prf.andE₂ ih
  | orI₁ h ih => sorry
  | orI₂ h ih => sorry
  | orE h hA hB ih ihA ihB => sorry
  | impI h ih => exact Prf.impI ih
  | impE h₁ h₂ ih₁ ih₂ => exact Prf.impE ih₁ ih₂
  | allI h ih => exact Prf.allI (by simpa using ih)
  | allE t h ih =>
      simpa [negative_subst] using Prf.allE t ih
  | exI t h ih => sorry
  | exE h₁ h₂ ih₁ ih₂ => sorry
  | eqRefl t => exact Prf.eqRefl t
  | eqSubst A σ τ hs hA ihs ihA =>
      simpa [negative_subst] using
        (Prf.eqSubst (negative A) σ τ ihs ihA)

/-- First recovery class. -/
inductive Retained : {n : Nat} → Fm PTm n → Prop
  | qf {n : Nat} {A : Fm PTm n} (h : A.QF) : Retained A
  | and {n : Nat} {A B : Fm PTm n}
      (hA : Retained A) (hB : Retained B) : Retained (A ⋏ B)
  | imp {n : Nat} {A B : Fm PTm n}
      (hA : Retained A) (hB : Retained B) : Retained (A ⟶ B)
  | all {n : Nat} {A : Fm PTm (n + 1)}
      (hA : Retained A) : Retained (Fm.all A)

/-- QF recovery uses syntax-directed Boolean decidability. -/
theorem qf_recovery_target {n : Nat} (A : Fm PTm n) (hA : A.QF) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff (negative A) A := by
  sorry

/-- Recovery on the retained class. -/
theorem retained_iff_target {n : Nat} {A : Fm PTm n}
    (h : Retained A) :
    ([] : List (Fm PTm n)) ⊢[PRAAx] Fm.iff (negative A) A := by
  induction h with
  | qf hqf => exact qf_recovery_target _ hqf
  | and hA hB ihA ihB => sorry
  | imp hA hB ihA ihB => sorry
  | all hA ih => sorry

/-- Lift an intuitionistic iPRA derivation into the classical source theory. -/
theorem lift_prf_target {n : Nat}
    {Γ : List (Fm PTm n)} {A : Fm PTm n}
    (h : Γ ⊢[PRAAx] A) : Γ ⊢[ClassicalPRAAx] A := by
  induction h <;> try constructor <;> try assumption
  all_goals sorry

/-- Final retained transfer theorem. -/
theorem retained_transfer_target {n : Nat}
    (Γ : List (Fm PTm n)) (A : Fm PTm n)
    (hΓ : ∀ B ∈ Γ, Retained B) (hA : Retained A) :
    (Γ ⊢[ClassicalPRAAx] A) ↔ (Γ ⊢[PRAAx] A) := by
  constructor
  · intro h
    have hn := translate_prf_target h
    have hn' : Γ ⊢[PRAAx] negative A := by
      apply hn.trans
      intro B hB
      rcases List.mem_map.mp hB with ⟨C, hC, rfl⟩
      have hiff := retained_iff_target (hΓ C hC)
      exact Prf.iffMpr hiff Prf.hyp0
    exact Prf.iffMp (retained_iff_target hA) hn'
  · exact lift_prf_target

end LeanProofs.KIFC.RetainedTransfer
