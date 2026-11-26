import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductT7
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductNamedT3
import IPRADerivations.Analysis.Trigonometry.SineProducts.GaussianSineProductT4Actual
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionR3Domain
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Reflection.GaussianGammaReflectionQuotient

/-!
# The original sine product and cleared Gamma reflection

The original sinc at πz is compared to the literal finite product via
the actual divided argument, its finite root factors, and the
synchronized comparison. The common cutoff also controls the literal
product tail. Cross-equivalence eliminates the cofinal observation
error and gives the reflection identity on the certified domain.
-/

set_option autoImplicit false
set_option maxHeartbeats 220000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductT7Actual

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaReflectionProduct (complementarySource complementaryData gammaPairF)
open GaussianGammaReflectionQuotient (reciprocalHeight quotientF quotientData apart_of_product quotient_of_cleared)
open GaussianGammaReflectionSineTransfer (sineAtPiF sineAtPiData productIdentification)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameReciprocal (apart)
open GaussianRationalDistanceOrder (distance_triangle_same)
open GaussianRationalLowerBounds (lower)
open GaussianSineProductReflectionLower (source numerator denominator)
open GaussianSineReflectionLower (threshold actual_sine_lower)
open GaussianSineProductNamedT3 (factoredF factoredDataAt factorization_at)
open GaussianSineProductT4Budget (halfIndex)
open GaussianSineProductT7 (cutoff cutoff_positive t4_cutoff_le prefixAt prefixRate product_identification)
open GaussianSineProductT4Actual (cofinalClock clock_later named_factored_distance precision_at)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem prefix_at (z R B x p : PTm n) (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] prefixAt z R B x (two+(one+one)) p := by
  let K := cutoff R p
  let J := halfIndex R K
  let q := cofinalClock z R B K x p
  let Y := factoredDataAt z R B J x one
  have hR := hs.andE₁
  have hB := hs.andE₂.andE₁
  have hz := hs.andE₂.andE₂
  have hK := cutoff_positive (Γ := Γ) R p
  have hA := (GaussianSineProductSynchronizedRow.argument_input z R B K x hR hK hB hz).andE₁
  have hT3 := factorization_at z R B J x one hB hz hA
  have hNear := named_factored_distance z R B K x p hR hK hB hz
  have hT4 := precision_at z R B K x p hR hK hB hz (t4_cutoff_le R p)
  exact GaussianSineProductT7.prefix_at factoredF z R B x p q Y (one+one) hT3
    (clock_later z R B K x p)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) hNear hT4)

theorem prefix_rate (z R B x : PTm n) (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] prefixRate z R B x (two+(one+one)) := by
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (a : PTm n) := Syn.shift a
  have h : Δ ⊢[PRAAx] GaussianGammaCanonicalExponent.source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hs.shift
  simpa only [prefixRate,Syn.shift,sh,Δ,PTm.subst_add,two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    prefix_at (sh z) (sh R) (sh B) (sh x) (var 0) h

theorem original_product_identification (z R B x : PTm n) (hs : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B) :
    Γ ⊢[PRAAx] productIdentification z R B x :=
  product_identification z R B x (two+(one+one)) hs (prefix_rate z R B x hs)

theorem original_cleared_reflection (z R B a d e f x : PTm n) (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF sineAtPiF gammaPairF) GaussianGammaHalfPiName.nameF
      (multiplyData sineAtPiF gammaPairF (sineAtPiData z B x) (complementaryData z R B d f)) x :=
  GaussianGammaReflectionSineTransfer.cleared_reflection z R B a d e f x hs
    (original_product_identification z R B x hs.andE₁.andE₁)

theorem original_sine_apart (z R B a d L x : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a d L) :
    Γ ⊢[PRAAx] apart sineAtPiF (reciprocalHeight d R L) (sineAtPiData z B x) :=
  apart_of_product z R B a d L x hs
    (original_product_identification z R B x (.andI hs.andE₁.andE₁.andE₁ (.andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₁)))

theorem original_sine_lower (z R B a d L p x : PTm n) (hs : Γ ⊢[PRAAx] source z R B a d L)
    (hp : Γ ⊢[PRAAx] le (threshold d R L) (unit p)) :
    Γ ⊢[PRAAx] lower (ap2 sineAtPiF p (sineAtPiData z B x)) (numerator a L) (denominator d R L) :=
  actual_sine_lower z R B a d L p x hs
    (original_product_identification z R B x (.andI hs.andE₁.andE₁.andE₁ (.andI hs.andE₁.andE₁.andE₂ hs.andE₂.andE₁))) hp

theorem original_reflection_quotient (z R B a d e f x : PTm n)
    (hs : Γ ⊢[PRAAx] complementarySource z R B a d e f) :
    Γ ⊢[PRAAx] crossEquivalent gammaPairF quotientF (complementaryData z R B d f)
      (quotientData z B x (reciprocalHeight d R (two*R))) :=
  quotient_of_cleared z R B a d e f x (reciprocalHeight d R (two*R)) hs
    (original_sine_apart z R B one d (two*R) x (GaussianGammaReflectionR3Domain.r3_source z R B a d e f hs))
    (original_cleared_reflection z R B a d e f x hs)

theorem actual_original_sine_product_T7_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianGammaCanonicalExponent.source (var 0) (var 1) (var 2) ⟶ productIdentification (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (original_product_identification _ _ _ _ Prf.hyp0))

theorem actual_original_cleared_Gamma_reflection_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        crossEquivalent (multiplyF sineAtPiF gammaPairF) GaussianGammaHalfPiName.nameF
          (multiplyData sineAtPiF gammaPairF (sineAtPiData (var 0) (var 2) (var 7))
            (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))) (var 7)) :=
  closeUniv 8 (.impI (original_cleared_reflection _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_sine_apart_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (GaussianSineProductReflectionLower.source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        apart sineAtPiF (reciprocalHeight (var 4) (var 1) (var 5)) (sineAtPiData (var 0) (var 2) (var 6))) :=
  closeUniv 7 (.impI (original_sine_apart _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_sine_R3_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      le (threshold (var 4) (var 1) (var 5)) (unit (var 6)) ⟶
        lower (ap2 sineAtPiF (var 6) (sineAtPiData (var 0) (var 2) (var 7)))
          (numerator (var 3) (var 5)) (denominator (var 4) (var 1) (var 5))) :=
  closeUniv 8 (.impI (.impI (original_sine_lower _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_original_Gamma_reflection_quotient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (complementarySource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
        crossEquivalent gammaPairF quotientF (complementaryData (var 0) (var 1) (var 2) (var 4) (var 6))
          (quotientData (var 0) (var 2) (var 7) (reciprocalHeight (var 4) (var 1) (two*var 1)))) :=
  closeUniv 8 (.impI (original_reflection_quotient _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSineProductT7Actual
