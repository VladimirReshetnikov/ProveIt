import IPRADerivations.Analysis.GaussianGammaRationalRatioBinding
import IPRADerivations.Analysis.GaussianStirlingMultiplicativeBoundsStrictOrder

/-!
# The strict rational Gautschi inequalities for the actual Gamma ratio

Strict exponential order transfers the exact logarithmic comparison
to the original power names and the certified actual Gamma quotient.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalGautschi

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianGammaRationalFractionalChord (harmonicF)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular fractional_real)
open GaussianGammaRationalLogGautschi (ratioExponentF ratioExponentData ratio_exponent_regular ratio_exponent_real)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_exponential_order)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianStirlingGammaLogarithm (gammaData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def powerF : PR 2 := E harmonicF
def powerData (r b a D : PTm n) : PTm n := ed harmonicF (fractionalData r b a D)
def ratioF : PR 2 := E ratioExponentF
def ratioData (a b r : PTm n) : PTm n := ed ratioExponentF (ratioExponentData a b r)

def gautschi (a b r s : PTm n) : Fm PTm n :=
  strictOrder powerF ratioF (powerData s b a b) (ratioData a b r) ⋏
    strictOrder ratioF powerF (ratioData a b r) (powerData s b (a+b) b)

theorem gautschi_order (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] gautschi a b r s := by
  have hn := ratio_exponent_regular a b r ha hb
  have hR := ratio_exponent_real (Γ := Γ) a b r
  exact .andI
    (strict_exponential_order _ _ _ _ (fractional_regular s b a b (.andI ha hb)) hn
      (fractional_real s b a b hb) hR (GaussianGammaRationalLogGautschi.lower a b r s ha hb hr hs he))
    (strict_exponential_order _ _ _ _ hn
      (fractional_regular s b (a+b) b (.andI (le_trans ha (le_add_right _ _)) hb)) hR
      (fractional_real s b (a+b) b hb) (GaussianGammaRationalLogGautschi.upper a b r s ha hb hr hs he))

def source (a b r s : PTm n) : Fm PTm n :=
  le one a ⋏ (le one b ⋏ (le one r ⋏ (le one s ⋏ b ≐ r+s)))

theorem actual_positive_rational_Gautschi_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ gautschi (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (gautschi_order _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

theorem actual_positive_rational_Gautschi_quotient_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 0) ⋏ le one (var 1)) ⟶ crossEquivalent
      (multiplyF ratioF GaussianGammaReciprocalInverse.gammaF) GaussianGammaReciprocalInverse.gammaF
      (multiplyData ratioF GaussianGammaReciprocalInverse.gammaF (ratioData (var 0) (var 1) (var 2))
        (gammaData (var 0+var 2) (var 1))) (gammaData (var 0+var 1) (var 1))) :=
  closeUniv 3 (.impI (GaussianGammaRationalRatioBinding.ratio_balance _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalGautschi
