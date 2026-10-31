import DiophantineConsistency.PRAWitnessRefutationOuter
import ZFCinPA.ZFDelta1

/-! The concrete Foundation ZFC refutation predicate, with the derivation
core's two witness bounds left as explicit assumptions. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessZFCCertificate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PRAStrictConReverse PRAWitnessRefutationOuter

local instance {N : Type} [Structure language N] : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {N : Type} [Structure language N] : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {N : Type} [Structure language N] : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {N : Type} [Structure language N] : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {N : Type} [Structure language N] : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem zfc_certificate_of_core
    (hσ : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], WB N (Derivation.blueprint (𝗭𝗙𝗖 : SetTheory)).core.sigma.val)
    (hπ : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], WB N (∼(Derivation.blueprint (𝗭𝗙𝗖 : SetTheory)).core.pi.val)) :
    BoundCertificate (provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)) :=
  certificate_of_core (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence) hσ hπ
end DiophantineConsistency.PRAWitnessZFCCertificate
