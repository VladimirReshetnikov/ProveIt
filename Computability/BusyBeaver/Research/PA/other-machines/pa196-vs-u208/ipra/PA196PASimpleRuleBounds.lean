import DiophantineConsistency.PRAWitnessPositiveSimpleRules
import DiophantineConsistency.PRAWitnessVerumRuleBranch
import DiophantineConsistency.PRAWitnessWeakeningRuleBranch
import DiophantineConsistency.PRAWitnessPositiveAndRule
import DiophantineConsistency.PRAWitnessPositiveOrRule
import DiophantineConsistency.PRAWitnessAndRuleBranch
import DiophantineConsistency.PRAWitnessOrRuleBranch
import Foundation.FirstOrder.Incompleteness.InductionSchemeDelta1

/-! Unconditional witness bounds for the exact verum, conjunction,
disjunction, and weakening branches
of Foundation PA's derivation core. Other rules and the PA axiom recognizer
are separate obligations. -/
set_option autoImplicit false
namespace PA196PASimpleRuleBounds
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus

noncomputable def positiveVerum : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or vrm _)) => vrm
  | _ => ⊥
noncomputable def negativeVerum : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or vrm _)) => vrm
  | _ => ⊥
noncomputable def positiveWeakening : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or wk _))))))) => wk
  | _ => ⊥
noncomputable def negativeWeakening : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or _ (.or wk _))))))) => wk
  | _ => ⊥
noncomputable def positiveAnd : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or a _))) => a
  | _ => ⊥
noncomputable def negativeAnd : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or a _))) => a
  | _ => ⊥
noncomputable def positiveOr : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val with
  | .and _ (.or _ (.or _ (.or _ (.or a _)))) => a
  | _ => ⊥
noncomputable def negativeOr : ArithmeticSemisentence 2 :=
  match (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val with
  | .and _ (.or _ (.or _ (.or _ (.or a _)))) => a
  | _ => ⊥

theorem positiveVerum_eq : positiveVerum =
    DiophantineConsistency.PRAWitnessPositiveSimpleRules.verumBranch := by rfl
theorem negativeVerum_eq : negativeVerum =
    DiophantineConsistency.PRAWitnessVerumRuleBranch.branch := by rfl
theorem positiveWeakening_eq : positiveWeakening =
    DiophantineConsistency.PRAWitnessPositiveSimpleRules.weakeningBranch := by rfl
theorem negativeWeakening_eq : negativeWeakening =
    DiophantineConsistency.PRAWitnessWeakeningRuleBranch.branch := by rfl
theorem positiveAnd_eq : positiveAnd =
    DiophantineConsistency.PRAWitnessPositiveAndRule.branch := by rfl
theorem negativeAnd_eq : negativeAnd =
    DiophantineConsistency.PRAWitnessAndRuleBranch.branch := by rfl
theorem positiveOr_eq : positiveOr =
    DiophantineConsistency.PRAWitnessPositiveOrRule.branch := by rfl
theorem negativeOr_eq : negativeOr =
    DiophantineConsistency.PRAWitnessOrRuleBranch.branch := by rfl

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_positiveVerum : WB M positiveVerum := by
  rw [positiveVerum_eq]
  exact DiophantineConsistency.PRAWitnessPositiveSimpleRules.wb_verum

theorem wb_negativeVerum : WB M (∼negativeVerum) := by
  rw [negativeVerum_eq]
  exact DiophantineConsistency.PRAWitnessVerumRuleBranch.wb_neg_branch

theorem wb_positiveWeakening : WB M positiveWeakening := by
  rw [positiveWeakening_eq]
  exact DiophantineConsistency.PRAWitnessPositiveSimpleRules.wb_weakening

theorem wb_negativeWeakening : WB M (∼negativeWeakening) := by
  rw [negativeWeakening_eq]
  exact DiophantineConsistency.PRAWitnessWeakeningRuleBranch.wb_neg_branch

theorem wb_positiveAnd : WB M positiveAnd := by
  rw [positiveAnd_eq]
  exact DiophantineConsistency.PRAWitnessPositiveAndRule.wb_branch

theorem wb_negativeAnd : WB M (∼negativeAnd) := by
  rw [negativeAnd_eq]
  exact DiophantineConsistency.PRAWitnessAndRuleBranch.wb_neg_branch

theorem wb_positiveOr : WB M positiveOr := by
  rw [positiveOr_eq]
  exact DiophantineConsistency.PRAWitnessPositiveOrRule.wb_branch

theorem wb_negativeOr : WB M (∼negativeOr) := by
  rw [negativeOr_eq]
  exact DiophantineConsistency.PRAWitnessOrRuleBranch.wb_neg_branch

#print axioms wb_positiveVerum
#print axioms wb_negativeVerum
#print axioms wb_positiveWeakening
#print axioms wb_negativeWeakening
#print axioms wb_positiveAnd
#print axioms wb_negativeAnd
#print axioms wb_positiveOr
#print axioms wb_negativeOr
end PA196PASimpleRuleBounds
