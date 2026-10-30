import DiophantineConsistency.PRAPositiveAdmissible
import DiophantineConsistency.ParsonsPositiveCertificate
/-! Unconditional candidate-PRA interpretation of positive-rule proofs. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsPositiveCandidate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory

theorem comparison {φ : Proposition ℒₒᵣ} (p : ParsonsPositiveRule.Proof 𝗣𝗔⁻ φ) :
    PRA ⊢ (Semiformula.lMap embedding φ).univCl :=
  ParsonsPositiveComparison.comparison PRAPositiveAdmissible.admissible p

theorem comparison_certified {φ : Proposition ℒₒᵣ} (p : ParsonsRule.Proof 𝗣𝗔⁻ φ)
    (h : ParsonsPositiveCertificate.AllPositive p) :
    PRA ⊢ (Semiformula.lMap embedding φ).univCl :=
  comparison (ParsonsPositiveCertificate.restrict p h)
end DiophantineConsistency.ParsonsPositiveCandidate
