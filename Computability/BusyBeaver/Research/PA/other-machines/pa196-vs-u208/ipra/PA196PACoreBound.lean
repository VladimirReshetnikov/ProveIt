import PA196ReverseGG
import DiophantineConsistency.PRAWitnessRefutationOuter

/-! The remaining PA witness bound reduced to two exact derivation-core
obligations. The two all-model bounds below are hypotheses, not theorems:
the available rule-leaf developments are for the set-theory language. -/
set_option autoImplicit false
noncomputable section
namespace PA196PACoreBound
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory
open DiophantineConsistency.PRAWitnessCalculus
open DiophantineConsistency.IPRAPA196Consistency

local instance {N : Type} [Structure language N] : Zero N :=
  ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance {N : Type} [Structure language N] : One N :=
  ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance {N : Type} [Structure language N] : Add N :=
  ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance {N : Type} [Structure language N] : Mul N :=
  ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance {N : Type} [Structure language N] : LT N :=
  ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

/-- Positive branch of Foundation PA's actual derivation core, for every
classical PRA model in the primitive-recursive language. -/
def PositiveCoreBound : Prop :=
  ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
    [N↓[language] ⊧* PRA],
    WB N (Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.sigma.val

/-- Negative pi branch of Foundation PA's actual derivation core, with the
same all-model scope. -/
def NegativeCoreBound : Prop :=
  ∀ (N : Type) [Nonempty N] [Structure language N] [Structure.Eq language N]
    [N↓[language] ⊧* PRA],
    WB N (∼(Derivation.blueprint (𝗣𝗔 : ArithmeticTheory)).core.pi.val)

/-- The exact PA witness-bound certificate follows from these two separate
arithmetical core obligations. -/
theorem boundCertificate_of_core (positive : PositiveCoreBound) (negative : NegativeCoreBound) :
    PA196ReverseGG.BoundCertificate := by
  simpa only [PA196ReverseGG.BoundCertificate,
    DiophantineConsistency.PRAStrictConReverse.BoundCertificate, paRefutation] using
    (DiophantineConsistency.PRAWitnessRefutationOuter.certificate_of_core
      (𝗣𝗔 : ArithmeticTheory) (⊥ : ArithmeticSentence) positive negative)

#print axioms boundCertificate_of_core
end PA196PACoreBound
