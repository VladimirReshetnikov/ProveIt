import DiophantineConsistency.HACurrentPolynomialBridge2011
import DiophantineConsistency.ArithmeticLocalNormalization

/-! # HA proves: the current equation has no positive zero ↔ ZFC is consistent

The finitary endpoint for the maintained current Diophantine equation. Every
link is an internal argument valid in every model of `𝗜𝚺₁` (at arbitrary,
possibly nonstandard, internal codes, times and sizes), so completeness yields an
actual `𝗜𝚺₁` proof (hence PRA-provable by Parsons' theorem), a PA proof, and the Gödel–Gentzen transfer yields an
actual derivation in the repository's Heyting-arithmetic calculus:

* polynomial bridge (`HACurrentPolynomialBridge2011.polynomialBridge`):
  soundness `ArithmeticSoundness2011` (positive zero ⇒ the decimal215 run halts)
  and construction `ArithmeticCurrentConstruction2011` (halt ⇒ positive zero),
  the latter with the finite Local Normalization Lemma, proved here Matrix-free
  (`ArithmeticLocalNormalization.localNormalization`);
* checker/machine theorem (`ArithmeticCheckerMachine215`);
* source bridge (`HACurrentAssembly2011.sourceBridge`, via
  `ZFCinPA.ValidatorConsistency222`): ZFC consistency ↔ no accepted C222
  refutation.

Standard-model truth is never promoted to provability, so the argument does not
use Lean's own proof of `Con(ZFC)`: the same theorem for a trivially unsolvable
equation would require HA to prove `Con(ZFC)`. -/
set_option autoImplicit false
set_option Elab.async false

namespace DiophantineConsistency.HACurrentEquation2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HACurrentAssembly2011 HACurrentPolynomialBridge2011 FoundationHADeltaZeroGG

/-- The polynomial bridge holds in every model of `𝗜𝚺₁`. -/
theorem polynomialBridge : PolynomialBridge :=
  HACurrentPolynomialBridge2011.polynomialBridge
    (constructionBridge ArithmeticLocalNormalization.localNormalization)

/-- **`𝗜𝚺₁` proves** the literal no-zero sentence equivalent to `Con(ZFC)`.
Both sides are Π₁, so the equivalence is Π₂ and, by Parsons' theorem, also
provable in primitive recursive arithmetic. -/
theorem isigma1_proves_current_iff_consistency :
    𝗜𝚺₁ ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence :=
  HACurrentAssembly2011.isigma1_proves_current_iff_consistency polynomialBridge sourceBridge

/-- **`𝗜𝚺₂` proves** the literal no-zero sentence equivalent to `Con(ZFC)`. -/
theorem isigma2_proves_current_iff_consistency :
    𝗜𝚺 2 ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence :=
  HACurrentAssembly2011.isigma2_proves_current_iff_consistency polynomialBridge sourceBridge

/-- **PA proves** the literal no-zero sentence equivalent to `Con(ZFC)`. -/
theorem peano_proves_current_iff_consistency :
    Peano ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence :=
  HACurrentAssembly2011.peano_proves_current_iff_consistency polynomialBridge sourceBridge

/-- **HA proves** that the literal current equation has no positive zero iff ZFC
proves no contradiction: an actual derivation, in the repository's HA calculus,
of the equivalence between `ArithmeticCurrentEquation2011.unsolvabilitySentence`
and the ordinary negation of the positive ZFC-refutation predicate. -/
theorem ha_current_iff_consistency :
    ProofEquiv ArithmeticCurrentEquation2011.unsolvabilitySentence
      FoundationHAConsistencyNormalization.ordinaryConsistency :=
  ha_current_iff_consistency_of_local ArithmeticLocalNormalization.localNormalization

end DiophantineConsistency.HACurrentEquation2011
