import DiophantineConsistency.PRAWitnessNegativePiCore
import DiophantineConsistency.PRAWitnessZFCAxioms
/-! The actual Foundation ZFC derivation core has bounded witnesses in the
negative pi polarity in every candidate-PRA model. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessZFCNegativePiCore
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus LeanProofs.ZFCinPA
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_neg_zfcCorePi : WB M (∼(Derivation.blueprint (𝗭𝗙𝗖 : SetTheory)).core.pi.val) := by
  exact PRAWitnessNegativePiCore.wb_neg_corePi (𝗭𝗙𝗖 : SetTheory)
    (PRAWitnessZFCAxioms.goodCh_zfc (M := M)).2
end DiophantineConsistency.PRAWitnessZFCNegativePiCore
