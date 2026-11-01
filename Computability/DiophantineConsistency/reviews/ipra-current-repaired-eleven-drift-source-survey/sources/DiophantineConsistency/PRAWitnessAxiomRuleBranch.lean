import DiophantineConsistency.PRAWitnessArithmetic
import ZFCinPA.Instances
/-! Conditional witness bound for the literal negative pi axiom disjunct
of Foundation’s derivation core, for any Δ₁ set theory. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessAxiomRuleBranch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAWitnessCalculus PRAWitnessArithmetic
variable (T : SetTheory) [T.Δ₁]
noncomputable def branch : ArithmeticSemisentence 2 :=
  “D C. ∃ s < D, ∃ p < D, !axmGraph D s p ∧ p ∈ s ∧ !T.Δ₁ch.pi p”
noncomputable def actualAxiomBranch : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint T).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ axm))))))))) => axm
  | _ => ⊥
theorem actualAxiomBranch_eq : actualAxiomBranch T = branch T := by rfl
variable {M : Type} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻]
theorem wb_neg_branch (hch : WB M (∼T.Δ₁ch.pi.val)) : WB M (∼branch T) := by
  have := wb_neg_axmGraph (M := M)
  have := wb_neg_bitDef (M := M)
  have := hch
  simp only [branch]
  wb_auto
theorem wb_neg_actualAxiomBranch (hch : WB M (∼T.Δ₁ch.pi.val)) : WB M (∼actualAxiomBranch T) := by
  rw [actualAxiomBranch_eq]
  exact wb_neg_branch T hch
end DiophantineConsistency.PRAWitnessAxiomRuleBranch
