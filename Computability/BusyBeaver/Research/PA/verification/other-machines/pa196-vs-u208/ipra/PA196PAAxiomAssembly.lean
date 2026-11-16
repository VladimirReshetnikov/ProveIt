import PA196PAMinusWitness
import PA196PAAxiomBound

/-! The exact two PA derivation axiom branches have bounded witnesses if the
positive and negative witness bounds for the unrestricted induction-schema
recognizer hold. The induction bounds remain explicit hypotheses. -/
set_option autoImplicit false
noncomputable section
namespace PA196PAAxiomAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.PRAWitnessCalculus
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Compose the exact recognizer and branch bounds, retaining both induction
schema bounds in the single `GoodCh` hypothesis. -/
theorem axiom_branches_of_induction
    (hind : PA196PAMinusWitness.GoodCh InductionScheme.delta1_univ M) :
    WB M PA196PAAxiomBound.actualPositive ∧ WB M (∼PA196PAAxiomBound.actualNegative) := by
  have h := PA196PAMinusWitness.good_pa_of_induction hind
  exact ⟨PA196PAAxiomBound.wb_positiveBranch h.1,
    PA196PAAxiomBound.wb_negativeBranch h.2⟩

#print axioms axiom_branches_of_induction
end PA196PAAxiomAssembly
