import DiophantineConsistency.PRAWitnessDerivationCoreLeft
import DiophantineConsistency.PRAWitnessIdentityRuleBranch
import DiophantineConsistency.PRAWitnessVerumRuleBranch
import DiophantineConsistency.PRAWitnessAndRuleBranch
import DiophantineConsistency.PRAWitnessOrRuleBranch
import DiophantineConsistency.PRAWitnessAllRuleBranch
import DiophantineConsistency.PRAWitnessExsRuleBranch
import DiophantineConsistency.PRAWitnessWeakeningRuleBranch
import DiophantineConsistency.PRAWitnessShiftRuleBranch
import DiophantineConsistency.PRAWitnessCutRuleBranch
import DiophantineConsistency.PRAWitnessAxiomRuleBranch
/-! Complete negative pi witness bound for the actual Foundation derivation
core, conditional only on the theory axiom recognizer bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessNegativePiCore
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus PRAWitnessDerivationCoreLeft
variable (T : SetTheory) [T.Δ₁]
noncomputable def assembledTail : ArithmeticSemisentence 2 :=
  PRAWitnessIdentityRuleBranch.branch ⋎ PRAWitnessVerumRuleBranch.branch ⋎
  PRAWitnessAndRuleBranch.branch ⋎ PRAWitnessOrRuleBranch.branch ⋎
  PRAWitnessAllRuleBranch.branch ⋎ PRAWitnessExsRuleBranch.branch ⋎
  PRAWitnessWeakeningRuleBranch.branch ⋎ PRAWitnessShiftRuleBranch.branch ⋎
  PRAWitnessCutRuleBranch.branch ⋎ PRAWitnessAxiomRuleBranch.branch T

theorem piTail_eq : piTail T = assembledTail T := by rfl
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
theorem wb_neg_piTail (hch : WB M (∼T.Δ₁ch.pi.val)) : WB M (∼piTail T) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  rw [piTail_eq]
  simp only [assembledTail, DeMorgan.or]
  exact wb_and PRAWitnessIdentityRuleBranch.wb_neg_branch
    (wb_and PRAWitnessVerumRuleBranch.wb_neg_branch
    (wb_and PRAWitnessAndRuleBranch.wb_neg_branch
    (wb_and PRAWitnessOrRuleBranch.wb_neg_branch
    (wb_and PRAWitnessAllRuleBranch.wb_neg_branch
    (wb_and PRAWitnessExsRuleBranch.wb_neg_branch
    (wb_and PRAWitnessWeakeningRuleBranch.wb_neg_branch
    (wb_and PRAWitnessShiftRuleBranch.wb_neg_branch
    (wb_and PRAWitnessCutRuleBranch.wb_neg_branch (PRAWitnessAxiomRuleBranch.wb_neg_branch T hch)))))))))

theorem wb_neg_corePi (hch : WB M (∼T.Δ₁ch.pi.val)) :
    WB M (∼(Derivation.blueprint T).core.pi.val) :=
  wb_neg_corePi_of_tail T (wb_neg_piTail T hch)
end DiophantineConsistency.PRAWitnessNegativePiCore
