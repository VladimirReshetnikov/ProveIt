import IPRADerivations.Analysis.Gamma.GaussianGammaRationalWendelGautschi
import IPRADerivations.Analysis.Gamma.GaussianGammaRationalRatioBinding

/-!
# Binding the Wendel relative name to the original Gamma quotient

The actual exponential of the relative logarithm times the original
denominator `x^u Γ(x)` recovers the actual numerator `Γ(x+u)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelBinding

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (exponentialInputData exponential_input)
open GaussianGammaRationalFractionalChord (harmonicF)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular)
open GaussianGammaRationalLogGautschi (ratioExponentF ratioExponentData ratio_exponent_regular fractional_sum)
open GaussianGammaRationalLogWendel (relativeExponentF relativeExponentData relative_exponent_regular)
open GaussianGammaRationalRatioBinding (difference_add_recover)
open GaussianGammaRationalGautschi (powerF powerData)
open GaussianGammaRationalWendelGautschi (relativeF relativeData)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_commutative add_associative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular gammaData gamma_regular)
open GaussianStirlingLogDuplication (exponential_regular exponential_gamma exponential_sum)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => harmonicF
local notation "P" => logGammaF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData
local notation "G" => GaussianGammaReciprocalInverse.gammaF
local notation "D" => ratioExponentF

def denominatorExponentF : PR 2 := addF L P
def denominatorExponentData (a b r : PTm n) : PTm n := addData (fractionalData r b a b) (logGammaData a b)
def denominatorF : PR 2 := multiplyF powerF G
def denominatorData (a b r : PTm n) : PTm n := multiplyData powerF G (powerData r b a b) (gammaData a b)

theorem logarithmic_balance (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] crossEquivalent (addF relativeExponentF denominatorExponentF) P
      (addData (relativeExponentData a b r s) (denominatorExponentData a b r)) (logGammaData (a+r) b) := by
  let N := negativeF D
  let R := denominatorExponentF
  let x := logGammaData a b
  let y := logGammaData (a+r) b
  let z := logGammaData (a+b) b
  let k := ratioExponentData a b r
  let n := negativeData k
  let u := fractionalData r b a b
  let v := fractionalData s b a b
  let q := denominatorExponentData a b r
  have hX : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hZ : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hx := log_gamma_regular a b hX
  have hy := log_gamma_regular (a+r) b hY
  have hz := log_gamma_regular (a+b) b hZ
  have hk := ratio_exponent_regular a b r ha hb
  have hn := negative_fast D k hk
  have hu := fractional_regular r b a b hX
  have hv := fractional_regular s b a b hX
  have hq := add_fast _ _ _ _ hu hx
  have a₁ := add_associative L N R v n q hv hn hq
  have a₂ := add_cross L L (addF N R) (addF R N) v v (addData n q) (addData q n)
    hv hv (add_fast _ _ _ _ hn hq) (add_fast _ _ _ _ hq hn) (cross_refl _ _ hv)
    (add_commutative N R n q hn hq)
  have a₃ := cross_symm _ _ _ _ (add_associative L R N v q n hv hq hn)
  have aEq := cross_trans _ _ _ _ _ _ a₁ (cross_trans _ _ _ _ _ _ a₂ a₃)
  have left₁ := cross_symm _ _ _ _ (add_associative L L P v u x hv hu hx)
  have left₂ := add_cross (addF L L) H P P (addData v u) (hd a b) x x (add_fast _ _ _ _ hv hu)
    (GaussianHarmonicLogarithmName.name_regular a b hX) hx hx
    (fractional_sum a b b s r hb (he.eqTrans (add_comm r s)) hX) (cross_refl _ _ hx)
  have left₃ := cross_symm _ _ _ _ (GaussianStirlingGammaLogShift.log_gamma_increment a b hX)
  have lEq := cross_trans _ _ _ _ _ _ left₁ (cross_trans _ _ _ _ _ _ left₂ left₃)
  have bEq := add_cross (addF L R) P N N (addData v q) z n n (add_fast _ _ _ _ hv hq) hz hn hn lEq (cross_refl _ _ hn)
  have diff := difference_add_recover P P z y hz hy
  have comp := cross_trans _ _ _ _ _ _ (add_commutative P D y k hy hk) diff
  have cEq := add_cross P (addF P D) N N z (addData y k) n n hz
    (add_fast _ _ _ _ hy hk) hn hn (cross_symm _ _ _ _ comp) (cross_refl _ _ hn)
  have dEq := GaussianNamedStrictOrderDifference.sum_sub_right P D y k hy hk
  exact cross_trans _ _ _ _ _ _ aEq (cross_trans _ _ _ _ _ _ bEq (cross_trans _ _ _ _ _ _ cEq dEq))

theorem denominator_exponential (a b r : PTm n) (hs : Γ ⊢[PRAAx] source a b) :
    Γ ⊢[PRAAx] crossEquivalent denominatorF (E denominatorExponentF) (denominatorData a b r)
      (ed denominatorExponentF (denominatorExponentData a b r)) := by
  let p := fractionalData r b a b
  let g := logGammaData a b
  let x := ed L p
  let y := gammaData a b
  have hp := fractional_regular r b a b hs
  have hg := log_gamma_regular a b hs
  have hx := exponential_regular L p hp
  have term := GaussianGammaAdjacentCutoff.multiply_cross powerF powerF G (E P) x x y (ed P g) hx hx
    (gamma_regular a b hs) (exponential_regular P g hg) (cross_refl _ _ hx) (cross_symm _ _ _ _ (exponential_gamma a b hs))
  exact cross_trans _ _ _ _ _ _ term (exponential_sum L P p g hp hg)

theorem ratio_balance (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF relativeF denominatorF) G
      (multiplyData relativeF denominatorF (relativeData a b r s) (denominatorData a b r))
      (gammaData (a+r) b) := by
  let F := relativeExponentF
  let R := denominatorExponentF
  let x := relativeExponentData a b r s
  let y := denominatorExponentData a b r
  let z := logGammaData (a+r) b
  let U (f : PR 2) (x : PTm n) := GaussianNameBounds.U f x
  have hX : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hx := relative_exponent_regular a b r s ha hb
  have hy := add_fast _ _ _ _ (fractional_regular r b a b hX) (log_gamma_regular a b hX)
  have hz := log_gamma_regular (a+r) b hY
  have pr := exponential_regular F x hx
  have den := multiply_fast powerF G _ _ (exponential_regular L _ (fractional_regular r b a b hX))
    (gamma_regular a b hX)
  have first := GaussianGammaAdjacentCutoff.multiply_cross relativeF relativeF denominatorF (E R)
    (ed F x) (ed F x) (denominatorData a b r) (ed R y) pr pr den (exponential_regular R y hy)
    (cross_refl _ _ pr) (denominator_exponential a b r hX)
  have second := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent F R P (U F x) (U R y) (U P z) x y z
    (exponential_input _ _ hx) (exponential_input _ _ hy) (exponential_input _ _ hz) (logarithmic_balance a b r s ha hb he)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ second (exponential_gamma (a+r) b hY))

theorem actual_positive_rational_Wendel_quotient_binding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((le one (var 0) ⋏ (le one (var 1) ⋏ var 1 ≐ var 2+var 3)) ⟶
      crossEquivalent (multiplyF relativeF denominatorF) G
        (multiplyData relativeF denominatorF (relativeData (var 0) (var 1) (var 2) (var 3))
          (denominatorData (var 0) (var 1) (var 2))) (gammaData (var 0+var 2) (var 1))) :=
  closeUniv 4 (.impI (ratio_balance _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaRationalWendelBinding
