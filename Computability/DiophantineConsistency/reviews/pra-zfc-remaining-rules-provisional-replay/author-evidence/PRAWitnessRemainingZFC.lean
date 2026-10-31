import DiophantineConsistency.PRAWitnessPositiveRuleAssembly
import ZFCinPA.ZFDelta1

/-! Reduce the exact ZFC refutation certificate to the remaining rule leaves. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessRemainingZFC
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LeanProofs.ZFCinPA PRAFiniteFunctionCodes PRALanguage PRATheory PRAWitnessCalculus
  PRAWitnessNegativeRuleAssembly PRAWitnessPositiveRuleAssembly PRAWitnessRefutationOuter
  PRAStrictConReverse
local instance {N : Type} [Structure language N] : Zero N := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {N : Type} [Structure language N] : One N := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {N : Type} [Structure language N] : Add N := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {N : Type} [Structure language N] : Mul N := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {N : Type} [Structure language N] : LT N := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

def PositiveRemainder (N : Type) [Structure language N] : Prop :=
  WB N (sigmaRule (𝗭𝗙𝗖 : SetTheory) 3) ∧ WB N (sigmaRule (𝗭𝗙𝗖 : SetTheory) 4) ∧
  WB N (sigmaRule (𝗭𝗙𝗖 : SetTheory) 5) ∧ WB N (sigmaRule (𝗭𝗙𝗖 : SetTheory) 8) ∧
  WB N (sigmaRule (𝗭𝗙𝗖 : SetTheory) 9)

def NegativeRemainder (N : Type) [Structure language N] : Prop :=
  WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 1) ∧ WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 2) ∧
  WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 3) ∧ WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 4) ∧
  WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 5) ∧ WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 8) ∧
  WB N (∼piRule (𝗭𝗙𝗖 : SetTheory) 9)

/-- Both remainder families are explicit model-wise hypotheses. -/
theorem zfc_certificate_of_remaining
    (hpos : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], PositiveRemainder N)
    (hneg : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], NegativeRemainder N) :
    BoundCertificate (provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)) := by
  apply certificate_of_core (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)
  · intro N _ _ _ _
    obtain ⟨h3,h4,h5,h8,h9⟩ := hpos N
    exact wb_coreSigma_of_remaining _ h3 h4 h5 h8 h9
  · intro N _ _ _ _
    obtain ⟨h1,h2,h3,h4,h5,h8,h9⟩ := hneg N
    exact wb_neg_corePi_of_remaining _ h1 h2 h3 h4 h5 h8 h9

/-- The literal candidate-PRA equation comparison, conditional on its IΣ₁
comparison and on the explicitly remaining rule-leaf bounds. -/
theorem zfc_comparison_of_remaining (n : ℕ) (a b : Semiterm ℒₒᵣ Empty n)
    (hsigma : Hierarchy 𝚺 1 (provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)))
    (heq : 𝗜𝚺₁ ⊢ (PRANoZeroUnary.noZero n a b 🡘
      ∼(provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence))))
    (hpos : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], PositiveRemainder N)
    (hneg : ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
      [N↓[language] ⊧* PRA], NegativeRemainder N) :
    PRA ⊢ (Semiformula.lMap embedding (PRANoZeroUnary.noZero n a b) 🡘
      Semiformula.lMap embedding (∼(provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)))) :=
  comparison_if_bound n a b _ hsigma heq (zfc_certificate_of_remaining hpos hneg)
end DiophantineConsistency.PRAWitnessRemainingZFC
