import IPRADerivations.Foundations.TAPIR.SearchK
import IPRADerivations.Foundations.BoundedReflection

/-!
# Compositional reflected formulas (formalization blueprint)

For each fixed formula, `Reflected phi` packages a concrete bit term and
ordinary object derivations of bit-valuedness, soundness, and completeness.
Meta-level recursion constructs these packages; iPRA never interprets an
arbitrary encoded formula.
-/

namespace LeanProofs.IPRA.TAPIR

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.BoundedReflection
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

/-- Closed reflection package, reusable under arbitrary hypotheses by
`Prf.ofNil` and under substitutions by `Prf.subst`. -/
structure Reflected {n : ℕ} (φ : Fm PTm n) where
  bit : PTm n
  cases : ([] : List (Fm PTm n)) ⊢[PRAAx]
    ((bit ≐ zero) ⋎ (bit ≐ one))
  sound : ([] : List (Fm PTm n)) ⊢[PRAAx]
    ((bit ≐ one) ⟶ φ)
  complete : ([] : List (Fm PTm n)) ⊢[PRAAx]
    (φ ⟶ (bit ≐ one))

namespace Reflected

variable {n : ℕ} {φ ψ : Fm PTm n}

/-- Equality reflection using `eqb`. -/
def eq (a b : PTm n) : Reflected (a ≐ b) := by
  refine ⟨eqb a b, ?_, ?_, ?_⟩
  · exact eqb_cases a b
  · exact .impI (eq_of_eqb Prf.hyp0)
  · exact .impI (eqb_of_eq Prf.hyp0)

/-- Nonzero reflection using the sign bit. -/
def nonzero (a : PTm n) : Reflected (neg (a ≐ zero)) := by
  /- Use `sg_cases`, `sg_zero`, and `sg_succ`; keep the proof intuitionistic. -/
  sorry

/-- Conjunction is represented by multiplication of bits. -/
def and (A : Reflected φ) (B : Reflected ψ) : Reflected (φ ⋏ ψ) := by
  /- Instantiate the closed fields under the necessary case contexts and split
     on A.cases and B.cases. -/
  sorry

/-- Disjunction is represented by the sign of the sum of bits. -/
def or (A : Reflected φ) (B : Reflected ψ) : Reflected (φ ⋎ ψ) := by
  sorry

/-- Intuitionistic negation is reflected because `A` carries decidability. -/
def neg (A : Reflected φ) : Reflected (Fm.neg φ) := by
  sorry

/-- For a reflected antecedent, implication is `not phi or psi`. -/
def imp (A : Reflected φ) (B : Reflected ψ) : Reflected (φ ⟶ ψ) := by
  exact or (neg A) B

/-- Blueprint for a bounded universal family.  The first implementation may
restrict to one packed parameter and call the existing checked `allB`; the
final implementation should use generic-arity reflection. -/
def ball (body : PTm 2) (N x : PTm n) :
    Reflected (Fm.all
      (lt (var 0) (Syn.shift N) ⟶
       neg (inst2 body (var 0) (Syn.shift x) ≐ zero))) := by
  refine ⟨allB body N x, ?_, ?_, ?_⟩
  · exact all_cases body N x
  · exact .impI (all_reflect body Prf.hyp0)
  · exact .impI (all_intro body Prf.hyp0)

/-- Blueprint for a bounded existential family. -/
def bex (body : PTm 2) (N x : PTm n) :
    Reflected (Fm.ex
      (lt (var 0) (Syn.shift N) ⋏
       neg (inst2 body (var 0) (Syn.shift x) ≐ zero))) := by
  refine ⟨exB body N x, ?_, ?_, ?_⟩
  · exact ex_cases body N x
  · refine .impI ?_
    have hw := ex_elim body Prf.hyp0
    exact .exI (wit body N x) (.andI (Prf.andE₁ hw) (Prf.andE₂ hw))
  · refine .impI ?_
    exact Prf.exE Prf.hyp0 (ex_intro body (Prf.andE₂ Prf.hyp0) (Prf.andE₁ Prf.hyp0))

end Reflected

end LeanProofs.IPRA.TAPIR
