import IPRADerivations.Analysis.Gamma.Ratios.Gautschi.GaussianGammaRationalGautschi
import IPRADerivations.Analysis.Gamma.Ratios.Wendel.GaussianGammaRationalLogWendel
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication
import IPRADerivations.Analysis.Exponential.Names.Identities.GaussianExponentialInverse

/-!
# The strict rational Wendel and Gautschi inequalities

All powers and quotients are exponentials of their exact real
logarithmic names. Strict real exponential order transports the
closed logarithmic inequalities to the actual normalized programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelGautschi

open_ipra
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianGammaRationalGautschi (powerF powerData source)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular fractional_real)
open GaussianGammaRationalLogGautschi (ratioExponentF ratioExponentData ratio_exponent_regular ratio_exponent_real)
open GaussianGammaRationalLogWendel (relativeExponentF relativeExponentData relative_exponent_regular relative_exponent_real)
open GaussianNameEquivalence (cross_refl)
open GaussianNameRingLaws (oneF zeroF zero_at zero_fast)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_exponential_order strict_transport)
open GaussianStirlingLogDuplication (exponential_regular)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

def relativeF : PR 2 := E relativeExponentF
def relativeData (a b r s : PTm n) : PTm n := ed relativeExponentF (relativeExponentData a b r s)

def wendel (a b r s : PTm n) : Fm PTm n :=
  strictOrder powerF relativeF (powerData s b a (a+r)) (relativeData a b r s) ⋏
    strictOrder relativeF oneF (relativeData a b r s) (ratioExponentData a b r)

theorem zero_real (x : PTm n) : Γ ⊢[PRAAx] realSamples zeroF x := by
  refine .allI ?_
  have e := zero_at (Γ := Γ.map Fm.shift) (var 0) (Syn.shift x)
  exact .andI (GaussianRationalHorner.canonical_congr e GaussianRationalSyntheticDivision.qzero_canonical)
    (RationalGaussianEmbedding.axis_congr e.eqSymm RationalGaussianEmbedding.axis_zero)

theorem wendel_order (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] wendel a b r s := by
  let x := relativeExponentData a b r s
  let d := ratioExponentData a b r
  have hn := relative_exponent_regular a b r s ha hb
  have hR := relative_exponent_real a b r s hb
  have left := strict_exponential_order _ _ _ _
    (fractional_regular s b a (a+r) (.andI ha (le_trans ha (le_add_right _ _)))) hn
    (fractional_real s b a (a+r) hb) hR (GaussianGammaRationalLogWendel.lower a b r s ha hb hr hs he)
  have right := strict_exponential_order _ _ _ _ hn (zero_fast d) hR (zero_real d)
    (GaussianGammaRationalLogWendel.upper a b r s ha hb hr hs he)
  exact .andI left (strict_transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (exponential_regular relativeExponentF x hn))
    (GaussianExponentialInverse.zero_exponential_cross (GaussianNameBounds.U zeroF d) d) right)

theorem actual_positive_rational_Wendel_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) (var 3) ⟶ wendel (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (wendel_order _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelGautschi
