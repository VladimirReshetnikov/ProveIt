import IPRABridge.ComparisonBits
import DiophantineConsistency.IPRABoundedChild

/-! Check the comparison in an arbitrary Concise context and the exact
Foundation judgments used in bounded formulas. -/

set_option autoImplicit false
noncomputable section

namespace IPRABridge.Checks.ComparisonBits

open LeanProofs.ConciseIPRA (Fm PTm Prf PRAAx)
open scoped LeanProofs.ConciseIPRA.Fm
open LeanProofs.IPRA (eqb)
open DiophantineConsistency
open PRAIsZero (isZeroCode)

example {n : ℕ} {Γ : List (Fm PTm n)} (t : PTm n) :
    Prf PRAAx Γ (translatedApp isZeroCode ![t] ≐ eqb t PTm.zero) :=
  translated_isZeroCode t

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes (Code)
open PRALanguage (language)
open PRATheory (PRA)
open PRAOpenFormulaCompiler (notCode)
open IPRABitConvention (eq zero one)
open IPRANativeTheory (nativeTheory)
open IPRATheoryHilbertBridge (extended)
open IPRANativeFormula
open IPRABoundedChild (guard childBody)

example {n : ℕ} (c : Code n) (v : Fin n → Term language ℕ) :
    extended nativeTheory ⊢! (eq (.func c v) zero ⋎ eq (.func c v) one) 🡒
      (eq (.func (notCode c) v) zero 🡘 eq (.func c v) one) :=
  IPRANotBit.notBitConvention (c := c) (v := v)

example {n : ℕ} (c : Code (n + 1)) (φ : Semisentence language (n + 1))
    (hbit : PRA ⊢ PRACharacteristicBit.bitSentence c)
    (hcorrect : PRA ⊢ PRABoundedCharacteristic.oneCorrectSentence c φ)
    (v : Fin (n + 1) → Term language ℕ)
    (hback : ∀ u : Fin (n + 1) → Term language ℕ,
      extended nativeTheory ⊢! (Rew.embSubsts u ▹ φ)ᴺ 🡒 native (Rew.embSubsts u ▹ φ)) :
    extended nativeTheory ⊢! ∼∼(∃⁰ (guard v ⋏ childBody φ v)) 🡒 ∃⁰ (guard v ⋏ childBody φ v) :=
  IPRABoundedChild.stableFromClassical c φ hbit hcorrect v hback

#print axioms translated_isZeroCode
#print axioms IPRANotBit.notBitConvention
#print axioms IPRABoundedChild.stableFromClassical

end IPRABridge.Checks.ComparisonBits
