import IPRADerivations.Analysis.Stirling.AllOrders.Truncation.GaussianStirlingAllOrderReciprocalTaylorBound
import IPRADerivations.Analysis.Stirling.AllOrders.Bernoulli.GaussianStirlingAllOrderCentralBernoulliError
import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderKernel
import IPRADerivations.Analysis.Optimization.Convexity.RationalConvexFiniteModulus

/-!
# Actual reciprocal-power central-difference observations

The exact signed defect of the scaled central difference and the
second-derivative weight is the cleared fourth-order integer defect.
Both terms are the original normalized rational grid observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalWeightError

open_ipra
open GaussianStirlingAllOrderDiscreteParts (secondDifference)
open GaussianStirlingAllOrderReciprocalTaylor (secondCoefficient)
open GaussianStirlingAllOrderReciprocalTaylorBound (integerDefect integerBound integer_error)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalHorner (positive_product scalar_add_same scalar_congr scalar_rescale)
open GaussianFactorBudget (power_positive)
open RationalConvexFiniteModulus (rescale_natural)
open RationalArithmetic (multiply represents)
open RationalRepresentations (represents_add represents_multiply represents_negative)
open RationalValueBounds (upper radius radius_of_upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def power (e : ℕ) (x : PTm n) : PTm n := pw x (num e)
def weight (e : ℕ) (H M x : PTm n) : PTm n := fraction (power e (H*M)) (power e x)
def coefficient (e : ℕ) : PTm n := num (secondCoefficient e)
def scaledSecond (e : ℕ) (x H M : PTm n) : PTm n :=
  multiply (fraction (M*M) one)
    (secondDifference (weight e H M (monus x H)) (weight e H M x) (weight e H M (x+H)))
def derivative (e : ℕ) (x H M : PTm n) : PTm n :=
  fraction (coefficient e*power (e+2) (H*M)) (power (e+2) x)

def commonDen (e : ℕ) (x H : PTm n) : PTm n :=
  power (e+2) x*(power e (x+H)*power e (monus x H))

def outerScale (e : ℕ) (H M : PTm n) : PTm n := power e (H*M)*(M*M)

def scaledNumerator (e : ℕ) (x H M : PTm n) : ZT n :=
  ZT.ofNat (outerScale e H M*(x*x))*
    (ZT.ofNat ((power e (x+H)+power e (monus x H))*power e x) -
      ZT.ofNat (two*(power e (x+H)*power e (monus x H))))

def derivativeNumerator (e : ℕ) (x H M : PTm n) : PTm n :=
  (coefficient e*power (e+2) (H*M))*(power e (x+H)*power e (monus x H))

def errorNumerator (e : ℕ) (x H M : PTm n) : PTm n := outerScale e H M*integerBound e x H

private theorem center_positive (x H : PTm n) (hh : Γ ⊢[PRAAx] le H x)
    (hx : Γ ⊢[PRAAx] le one (monus x H)) : Γ ⊢[PRAAx] le one x :=
  le_trans hx (le_congr (.eqRefl _) (eq_add_of_le hh).eqSymm (le_add_left (monus x H) H))

theorem common_positive (e : ℕ) (x H : PTm n) (hh : Γ ⊢[PRAAx] le H x) (hx : Γ ⊢[PRAAx] le one (monus x H)) :
    Γ ⊢[PRAAx] le one (commonDen e x H) := by
  have hc := center_positive x H hh hx
  exact positive_product _ _ (power_positive _ _ hc)
    (positive_product _ _ (power_positive _ _ (le_trans hc (le_add_right _ _))) (power_positive _ _ hx))

theorem scaled_at (e : ℕ) (x H M : PTm n) (hh : Γ ⊢[PRAAx] le H x) (hx : Γ ⊢[PRAAx] le one (monus x H)) :
    Γ ⊢[PRAAx] represents (scaledSecond e x H M) (scaledNumerator e x H M) (commonDen e x H) := by
  let a := power e (x+H)
  let b := power e (monus x H)
  let c := power e x
  let P := power e (H*M)
  let u := weight e H M (x+H)
  let v := weight e H M x
  let w := weight e H M (monus x H)
  have hc := center_positive x H hh hx
  have hA : Γ ⊢[PRAAx] le one a := power_positive _ _ (le_trans hc (le_add_right _ _))
  have hB : Γ ⊢[PRAAx] le one b := power_positive _ _ hx
  have hC : Γ ⊢[PRAAx] le one c := power_positive _ _ hc
  have ha : Γ ⊢[PRAAx] represents u (ZT.ofNat P) a := fraction_represents _ _ hA
  have hb : Γ ⊢[PRAAx] represents w (ZT.ofNat P) b := fraction_represents _ _ hB
  have hv : Γ ⊢[PRAAx] represents v (ZT.ofNat P) c := fraction_represents _ _ hC
  have f := represents_add _ _ _ _ _ _ ha hb
  have g := represents_negative _ _ _ (scalar_add_same _ _ _ _ _ hC hv hv)
  have z := represents_add _ _ _ _ _ _ f g
  have za := represents_multiply _ _ _ _ _ _ (fraction_represents (M*M) one (le_refl one)) z
  have zr := scalar_rescale _ _ _ (x*x) za
  refine scalar_congr (.eqRefl _) ?_ ?_ zr
  · apply ZT.derive
    dsimp only [a,b,c,P,scaledNumerator,outerScale]
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat]
    ipra_simps
    ring
  · apply deriveNat
    dsimp only [a,b,c,commonDen,power]
    ipra_simps
    simp only [AnalyticNumberTheory.RobinThreePos.pw_lit,pow_add,pow_two]
    ring

theorem derivative_at (e : ℕ) (x H M : PTm n) (hh : Γ ⊢[PRAAx] le H x) (hx : Γ ⊢[PRAAx] le one (monus x H)) :
    Γ ⊢[PRAAx] represents (derivative e x H M) (ZT.ofNat (derivativeNumerator e x H M)) (commonDen e x H) :=
  rescale_natural _ _ _ _ _ (fraction_represents _ _ (power_positive _ _ (center_positive x H hh hx))) (.eqRefl _)

theorem cleared_identity (e : ℕ) (x H M : PTm n) :
    Γ ⊢[PRAAx] ZT.eq (scaledNumerator e x H M-ZT.ofNat (derivativeNumerator e x H M))
      (ZT.ofNat (outerScale e H M)*integerDefect e x H) := by
  have eq := natEq (AnalyticNumberTheory.LocalFactor.pw_mul_base (Γ := Γ) (x+H) (monus x H) (num e))
  apply ZT.derive
  dsimp only [scaledNumerator,derivativeNumerator,integerDefect,outerScale,coefficient,power]
  simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  rw [eq]
  simp only [AnalyticNumberTheory.RobinThreePos.pw_lit,pow_add,pow_two]
  ipra_simps
  ring

private theorem numerator_brackets (e : ℕ) (he : 2≤e) (x H M : PTm n) (hh : Γ ⊢[PRAAx] le H x) :
    let z := scaledNumerator e x H M-ZT.ofNat (derivativeNumerator e x H M)
    let U := errorNumerator e x H M
    (Γ ⊢[PRAAx] zle z (ZT.ofNat U)) ∧ (Γ ⊢[PRAAx] zle (-ZT.ofNat U) z) := by
  let K := outerScale e H M
  have err := integer_error e he x H hh
  have eq := ZT.toZ_eq (cleared_identity (Γ := Γ) e x H M)
  have hc := nn_term (Γ := Γ) K
  constructor
  · apply zle_of_comb (𝔞 K*zsl err.1)
    · simp only [zsl_def,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat,errorNumerator] at eq ⊢
      ipra_simps
      linear_combination -eq
    · exact nn_mul hc (nn_zsl err.1)
  · apply zle_of_comb (𝔞 K*zsl err.2)
    · simp only [zsl_def,ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat,errorNumerator] at eq ⊢
      ipra_simps
      linear_combination eq
    · exact nn_mul hc (nn_zsl err.2)

theorem curvature_error (e : ℕ) (he : 2≤e) (x H M : PTm n) (hh : Γ ⊢[PRAAx] le H x)
    (hx : Γ ⊢[PRAAx] le one (monus x H)) :
    Γ ⊢[PRAAx] radius (scaledSecond e x H M) (derivative e x H M) (errorNumerator e x H M) (commonDen e x H) := by
  let U := scaledSecond e x H M
  let V := derivative e x H M
  let a := scaledNumerator e x H M
  let b := ZT.ofNat (derivativeNumerator e x H M)
  let D := commonDen e x H
  let N := errorNumerator e x H M
  have hD := common_positive e x H hh hx
  have p := scaled_at e x H M hh hx
  have q := derivative_at e x H M hh hx
  have h := numerator_brackets e he x H M hh
  have forward : Γ ⊢[PRAAx] upper U V N D := by
    apply RationalRepresentedUpper.from_signed _ _ a b D D N D hD hD p q
    apply zle_of_comb (𝔞 D*𝔞 D*zsl h.1)
    · dsimp only [a,b,N]
      simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,zsl_def,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat]
      ipra_simps
      ring
    · exact nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_zsl h.1)
  have back : Γ ⊢[PRAAx] upper V U N D := by
    apply RationalRepresentedUpper.from_signed _ _ b a D D N D hD hD q p
    apply zle_of_comb (𝔞 D*𝔞 D*zsl h.2)
    · dsimp only [a,b,N]
      simp only [RationalRepresentedUpper.left,RationalRepresentedUpper.right,zsl_def,ZT.toZ_mul,ZT.toZ_add,
        ZT.toZ_sub,ZT.toZ_neg,ZT.toZ_ofNat]
      ipra_simps
      ring
    · exact nn_mul (nn_mul (nn_term _) (nn_term _)) (nn_zsl h.2)
  exact radius_of_upper _ _ _ _ forward back

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderReciprocalWeightError
