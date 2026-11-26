import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedClearedSincMultipleAngle
import IPRADerivations.Analysis.Trigonometry.Sinc.GaussianNamedSincCongruence
import IPRADerivations.Analysis.Trigonometry.SineProducts.Scaling.GaussianSineProductScaledZero
import IPRADerivations.Analysis.Trigonometry.SineProducts.Bounds.GaussianSineProductReflectionArgument

/-!
# T3 on the original encoded Gaussian argument

The reflection sinc is equivalent to the named sinc at the divided
argument times the normalized finite root product. Split on the
squared norm of the encoded numerator. In the positive case cancel
the scaled argument using its explicit apartness clock. In the zero
case use the exact value one for sinc and the normalized product.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSineProductNamedT3

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded normSq)
open GaussianArctangentDivisionAngles (modulus)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaReflectionSineTransfer (argumentF argumentRadius argumentData)
open GaussianNameArithmetic (multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedClearedSincMultipleAngle (rootFactorF rootFactorData root_factor_regular)
open GaussianRadiusExponentialName (input)
open GaussianSineProductScaledArgumentCancellation (apartClock scaled_apart)
open GaussianSineProductScaledArgumentIdentity (wide_input multiple_cross)
open GaussianSineProductScaledArguments (nameF data)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev factoredF : PR 2 := GaussianNamedClearedSincMultipleAngle.factoredF nameF

def factoredDataAt (z R B J x W : PTm n) : PTm n :=
  GaussianNamedClearedSincMultipleAngle.factoredData nameF J W (data z R B (modulus J) x) x

def factoredData (z R B J x : PTm n) : PTm n := factoredDataAt z R B J x (num 4*R)

theorem factored_regular_at (z R B J x W : PTm n) (ha : Γ ⊢[PRAAx] input nameF W (data z R B (modulus J) x)) :
    Γ ⊢[PRAAx] pointCN factoredF (factoredDataAt z R B J x W) := by
  let A := data z R B (modulus J) x
  exact multiply_fast (GaussianNamedSinc.nameF nameF) (rootFactorF nameF)
    (GaussianNamedSinc.data nameF W A) (rootFactorData nameF J W A x)
    (GaussianNamedSinc.name_regular _ _ _ ha) (root_factor_regular _ _ _ _ _ ha)

theorem factored_regular (z R B J x : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] bounded z (R*B)) : Γ ⊢[PRAAx] pointCN factoredF (factoredData z R B J x) :=
  factored_regular_at z R B J x (num 4*R) (wide_input z R B (modulus J) x hB (zero_lt_succ _) hz)

theorem scaled_factorization_at (z R B J x W : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] input nameF W (data z R B (modulus J) x)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedSinc.nameF (GaussianNamedNaturalScale.nameF nameF)) factoredF
      (GaussianNamedClearedSincMultipleAngle.scaledSincData nameF (modulus J) J W (data z R B (modulus J) x))
      (factoredDataAt z R B J x W) := by
  let m := modulus J
  let a := data z R B m x
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  refine .orE (zero_or_succ (normSq z)) ?_ ?_
  · exact GaussianSineProductScaledZero.zero_identity nameF W J m a x ha.wk (le_refl m)
      (GaussianSineProductScaledZero.scaled_zero_samples z R B m x hB.wk hm.wk Prf.hyp0)
  · have pos : (normSq z ≐ ConciseIPRA.PTm.succ (pred (normSq z))) :: Γ ⊢[PRAAx] le one (normSq z) :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact GaussianNamedClearedSincMultipleAngle.from_apart nameF m J W a x (apartClock B m)
      ha.wk (le_refl m) (scaled_apart z R B m x hB.wk hm.wk pos)

theorem reflection_input (z B x : PTm n) :
    Γ ⊢[PRAAx] input argumentF (argumentRadius z B x) (argumentData z B x) :=
  GaussianGammaFiniteApproximantName.exponential_input argumentF (argumentData z B x)
    (multiply_fast GaussianGammaHalfPiName.nameF GaussianGammaCanonicalExponent.constantF x
      (GaussianRationalHorner.ofGaussian z B) (GaussianGammaHalfPiName.name_regular x)
      (GaussianGammaCanonicalExponent.constant_regular _))

theorem factorization_at (z R B J x W : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] bounded z (R*B)) (ha : Γ ⊢[PRAAx] input nameF W (data z R B (modulus J) x)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedSinc.nameF argumentF) factoredF
      (GaussianNamedSinc.data argumentF (argumentRadius z B x) (argumentData z B x)) (factoredDataAt z R B J x W) := by
  let m := modulus J
  let f := GaussianNamedNaturalScale.nameF nameF
  let a := data z R B m x
  let F := GaussianNamedNaturalScale.radius m W
  let d := GaussianNamedNaturalScale.data m m a
  have hm : Γ ⊢[PRAAx] le one m := zero_lt_succ _
  have hf : Γ ⊢[PRAAx] input f F d :=
    GaussianNamedNaturalScale.exponential_input nameF m m W a ha (le_refl m)
  have argument := cross_trans _ _ _ _ _ _ (multiple_cross z R B m m x hB hm (le_refl m) hz)
    (GaussianSineProductReflectionArgument.reflection_argument_cross z R B x hB hz)
  have sf := GaussianNamedSincCongruence.sinc_proper f argumentF F (argumentRadius z B x) d (argumentData z B x)
    hf (reflection_input z B x) argument
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ sf) (scaled_factorization_at z R B J x W hB ha)

theorem factorization (z R B J x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hz : Γ ⊢[PRAAx] bounded z (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedSinc.nameF argumentF) factoredF
      (GaussianNamedSinc.data argumentF (argumentRadius z B x) (argumentData z B x)) (factoredData z R B J x) :=
  factorization_at z R B J x (num 4*R) hB hz (wide_input z R B (modulus J) x hB (zero_lt_succ _) hz)

theorem original_named_sinc_T3_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 2) ⟶ bounded (var 0) (var 1*var 2) ⟶
      crossEquivalent (GaussianNamedSinc.nameF argumentF) factoredF
        (GaussianNamedSinc.data argumentF (argumentRadius (var 0) (var 2) (var 4)) (argumentData (var 0) (var 2) (var 4)))
        (factoredData (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (.impI (factorization _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianSineProductNamedT3
