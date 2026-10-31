import DiophantineConsistency.PRAWitnessCoreRules
import DiophantineConsistency.PRAWitnessIdentityRuleBranch
import DiophantineConsistency.PRAWitnessWeakeningRuleBranch
import DiophantineConsistency.PRAWitnessShiftRuleBranch

/-! Assemble the literal pi-core rule leaves, discharging the checked identity,
weakening and shift branches. The seven other branches remain assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace DiophantineConsistency.PRAWitnessNegativeRuleAssembly
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PRAWitnessDerivationCoreLeft PRAWitnessCoreRules

def disjunctAt {n : ℕ} : ℕ → ArithmeticSemisentence n → ArithmeticSemisentence n
  | 0, .or a _ => a
  | i+1, .or _ b => disjunctAt i b
  | 0, a => a
  | _+1, _ => ⊥

noncomputable def piRule (T : SetTheory) [T.Δ₁] (i : ℕ) : ArithmeticSemisentence 2 :=
  disjunctAt i (piTail T)

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem negativeLeaves_of_remaining (T : SetTheory) [T.Δ₁]
    (h1 : WB M (∼piRule T 1)) (h2 : WB M (∼piRule T 2))
    (h3 : WB M (∼piRule T 3)) (h4 : WB M (∼piRule T 4))
    (h5 : WB M (∼piRule T 5)) (h8 : WB M (∼piRule T 8))
    (h9 : WB M (∼piRule T 9)) : NegativeLeaves (M := M) (piTail T) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have h0 : WB M (∼piRule T 0) := PRAWitnessIdentityRuleBranch.wb_neg_actualIdentityBranch T
  have h6 : WB M (∼piRule T 6) := PRAWitnessWeakeningRuleBranch.wb_neg_actualWeakeningBranch T
  have h7 : WB M (∼piRule T 7) := PRAWitnessShiftRuleBranch.wb_neg_actualShiftBranch T
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩

theorem wb_neg_corePi_of_remaining (T : SetTheory) [T.Δ₁]
    (h1 : WB M (∼piRule T 1)) (h2 : WB M (∼piRule T 2))
    (h3 : WB M (∼piRule T 3)) (h4 : WB M (∼piRule T 4))
    (h5 : WB M (∼piRule T 5)) (h8 : WB M (∼piRule T 8))
    (h9 : WB M (∼piRule T 9)) : WB M (∼(Derivation.blueprint T).core.pi.val) :=
  wb_neg_corePi_of_leaves T (negativeLeaves_of_remaining T h1 h2 h3 h4 h5 h8 h9)
end DiophantineConsistency.PRAWitnessNegativeRuleAssembly
