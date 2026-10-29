import DiophantineConsistency.ParsonsInductionCase
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsInductionCaseChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsInductionCase

example {L : Language} [L.ORing] (φ : Semiproposition L 1) (t : SyntacticTerm L) :
    (matrix φ)/[t] = base φ ⋏ (step φ ⋏ ∼(φ/[t])) := matrix_subst φ t

-- Actual Foundation induction axiom, including arbitrary open parameters.
example {L : Language} [L.ORing] (φ : Semiproposition L 1) :
    Derivation [succInd φ, ∃⁰ (matrix φ)] := induction_normalization φ

-- Recursive obligations refer to genuinely shorter cut-free derivations.
example {L : Language} [L.ORing] (φ : Semiproposition L 1) (t : SyntacticTerm L)
    (Γ : Sequent L) (d : Derivation ((matrix φ)/[t] :: Γ))
    (hc : Derivation.IsCutFree d) :
    (∃ e : Derivation (base φ :: Γ), Derivation.IsCutFree e ∧ e.height < d.exs.height) ∧
    (∃ e : Derivation (step φ :: Γ), Derivation.IsCutFree e ∧ e.height < d.exs.height) ∧
    (∃ e : Derivation (∼(φ/[t]) :: Γ), Derivation.IsCutFree e ∧ e.height < d.exs.height) :=
  invert_exists φ t Γ d hc

#print axioms matrix_subst
#print axioms matrix_free
#print axioms induction_normalization
#print axioms normalize_in_context
#print axioms invert_exists
#print axioms one_case
end DiophantineConsistency.ParsonsInductionCaseChecks
