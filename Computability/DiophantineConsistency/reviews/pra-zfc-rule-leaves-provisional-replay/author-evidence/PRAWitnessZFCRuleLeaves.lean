import DiophantineConsistency.PRAWitnessCoreRules
import ZFCinPA.ZFDelta1

/-! The exact ZFC refutation certificate reduces to its rule-leaf bounds. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessZFCRuleLeaves
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PRAWitnessDerivationCoreLeft PRAWitnessCoreRules PRAStrictConReverse
local instance {N : Type} [Structure language N] : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {N : Type} [Structure language N] : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {N : Type} [Structure language N] : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {N : Type} [Structure language N] : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {N : Type} [Structure language N] : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem zfc_certificate_of_rule_leaves
    (hpos : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], PositiveLeaves (M := N) (sigmaTail (𝗭𝗙𝗖 : SetTheory)))
    (hneg : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], NegativeLeaves (M := N) (piTail (𝗭𝗙𝗖 : SetTheory))) :
    BoundCertificate (provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)) :=
  certificate_of_rule_leaves (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence) hpos hneg
end DiophantineConsistency.PRAWitnessZFCRuleLeaves
