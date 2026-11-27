import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerExponentIncrement
import IPRADerivations.Analysis.Euler.CompactExhaustion.ParameterBounds.GaussianEulerCompactPowerMajorant
import IPRADerivations.Analysis.Exponential.Estimates.GaussianRadiusExponentialLipschitzRate
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence

/-!
# Comparing the original Euler power exponent to its linear shift

The actual exponent at the later time is compared to the original
earlier exponent plus its exact rational linear increment. The addition
keeps its actual observation clock. Both names have a uniform common
radius on the compact time interval, and the named comparison retains
the quadratic remainder and two independent observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerShiftRate

open_ipra
open GaussianEulerIntegrandName (powerExponentF powerExponentData power_exponent_regular)
open GaussianEulerPowerExponentIncrement (exponentSample increment linear linear_bound exponent_increment)
open GaussianEulerCompactPowerMajorant (exponentRadius exponent_sample)
open GaussianCompactLogarithmBounds (domain)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (addF addData add_at add_fast recode_congr)
open GaussianRationalHorner (qadd qadd_canonical qmul_canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalDistanceOrder (distance_radius_mono)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr qadd_sub_cancel)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRadiusExponentialName (boundedSamples)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedInverseRate (independentRate)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def source (z R B E T a b c : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏
  (domain a b E T ⋏ (domain (a+c) b E T ⋏ le ((R+one)*c) a))
def radius (R E T : PTm n) : PTm n := exponentRadius R E T+one
def shiftedF : PR 2 := addF powerExponentF constantF
def shiftedData (z B a b c : PTm n) : PTm n := addData (powerExponentData z B a b) (linear z B a c)
def shiftClock (p : PTm n) : PTm n := GaussianFastValueCut.exponent two p
def numerator (R c : PTm n) : PTm n := (R+one)*(c*c)

ipra_subst radius [exponentRadius]
ipra_subst shiftedData
ipra_subst numerator
ipra_subst source

theorem shifted_at (p z B a b c : PTm n) :
    Γ ⊢[PRAAx] ap2 shiftedF p (shiftedData z B a b c) ≐
      qadd (exponentSample (shiftClock p) z B a b) (linear z B a c) :=
  (add_at powerExponentF constantF (powerExponentData z B a b) (linear z B a c) p).eqTrans
    ((recode_congr (qadd_congr (.eqRefl _) (constant_at (shiftClock p) (linear z B a c)))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qadd_canonical _ _)))

theorem displaced_difference (x y d : PTm n) (hd : Γ ⊢[PRAAx] GaussianRationalHorner.canonical d) :
    Γ ⊢[PRAAx] qsub (qsub x y) d ≐ qsub x (qadd y d) := by
  have split : Γ ⊢[PRAAx] qadd (qsub x (qadd y d)) d ≐ qsub x y :=
    (qadd_congr (.eqRefl _) (qadd_sub_cancel y d hd).eqSymm).eqTrans
      (GaussianReconstructionRoots.difference_chain x (qadd y d) y)
  exact (qsub_congr split.eqSymm (.eqRefl _)).eqTrans
    (GaussianReciprocalHorner.qsub_add_cancel _ d (qsub_canonical _ _))

theorem shifted_diagonal (p z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] distanceBounded (ap2 powerExponentF p (powerExponentData z B (a+c) b))
      (ap2 shiftedF p (shiftedData z B a b c))
      (diagonalNumerator (numerator R c) (a*a) (two*(R+one)) p) (diagonalDenominator (a*a) p) := by
  let s := shiftClock p
  let P := unit p
  let U := unit s
  let A := a*a
  let K := R+one
  let x := exponentSample p z B (a+c) b
  let y := exponentSample s z B a b
  let d := linear z B a c
  have ha := h.andE₂.andE₁.andE₁.andE₁
  have hb := h.andE₂.andE₁.andE₁.andE₂
  have hA := positive_product a a ha ha
  have hP := unit_positive (Γ := Γ) p
  have hU := unit_positive (Γ := Γ) s
  have raw := exponent_increment p s z R B a b c h.andE₁.andE₁ h.andE₁.andE₂.andE₂ ha hb
  have read : Γ ⊢[PRAAx] qsub (qsub x y) d ≐ qsub x (ap2 shiftedF p (shiftedData z B a b c)) :=
    (displaced_difference x y d (qmul_canonical _ _)).eqTrans
      (qsub_congr (.eqRefl _) (shifted_at p z B a b c).eqSymm)
  have near := bound_congr read (.eqRefl _) (.eqRefl _) raw
  have order : Γ ⊢[PRAAx] le P U := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have compare : Γ ⊢[PRAAx] le
      (GaussianEulerPowerExponentIncrement.errorNumerator p s R a c*diagonalDenominator (a*a) p)
      (diagonalNumerator (numerator R c) (a*a) (two*(R+one)) p*
        GaussianEulerPowerExponentIncrement.errorDenominator p s a) := by
    change Γ ⊢[PRAAx] le ((K*((c*c)*(P*U)+(P+U)*A))*(A*P))
      (((K*(c*c))*P+(two*K)*A)*(A*(P*U)))
    ipra_le (𝔞 K*𝔞 A*𝔞 A*𝔞 P)*sl order
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ hA (positive_product _ _ hP hU)) (positive_product _ _ hA hP) compare near

theorem earlier_input (z R B E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E) (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input powerExponentF (exponentRadius R E T)
      (powerExponentData z B a b) := by
  refine .andI (power_exponent_regular z B a b (.andI h.andE₁ ht.andE₁)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (Syn.shift z) (Syn.shift R)
      (Syn.shift B) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using h.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa [boundedSamples,exponentRadius,Syn.shift] using
    exponent_sample (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T)
      (Syn.shift a) (Syn.shift b) hs ts

theorem unit_bound (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] bounded (linear z B a c) one one :=
  GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    h.andE₂.andE₁.andE₁.andE₁ (le_refl _)
    (le_congr (by ipra_ring) (by ipra_ring) h.andE₂.andE₂.andE₂)
    (linear_bound z R B a c h.andE₁.andE₁ h.andE₁.andE₂.andE₂ h.andE₂.andE₁.andE₁.andE₁)

theorem shifted_bound (p z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] bounded (ap2 shiftedF p (shiftedData z B a b c)) (radius R E T) one := by
  have first := exponent_sample (shiftClock p) z R B E T a b h.andE₁ h.andE₂.andE₁
  have sum := bounded_sum (exponentSample (shiftClock p) z B a b) (linear z B a c)
    (exponentRadius R E T) one one one (le_refl one) (le_refl one) first (unit_bound z R B E T a b c h)
  have reconcile : Γ ⊢[PRAAx] exponentRadius R E T*one+one*one ≐ radius R E T := by
    unfold radius
    ipra_ring
  exact bound_congr (shifted_at p z B a b c).eqSymm reconcile (one_mul one) sum

theorem shifted_input (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input shiftedF (radius R E T) (shiftedData z B a b c) := by
  refine .andI (add_fast _ _ _ _ (power_exponent_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁))
    (constant_regular _)) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E)
      (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [boundedSamples,Syn.shift] using shifted_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
    (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) hs

theorem later_input (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input powerExponentF (radius R E T) (powerExponentData z B (a+c) b) :=
  GaussianExponentialRadiusIndependence.input_widen _ _ _ _
    (earlier_input z R B E T (a+c) b h.andE₁ h.andE₂.andE₂.andE₁) (le_add_right _ _)

theorem linear_shift_rate (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] independentRate powerExponentF shiftedF (powerExponentData z B (a+c) b) (shiftedData z B a b c)
      (numerator R c) (a*a) := by
  have ha := h.andE₂.andE₁.andE₁.andE₁
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (two*(R+one))
    (positive_product _ _ ha ha) (later_input z R B E T a b c h).andE₁ (shifted_input z R B E T a b c h).andE₁
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E)
      (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [diagonalEnvelope,Syn.shift] using shifted_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
    (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) hs

theorem original_exponential_comparison_input (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialLipschitzRate.input powerExponentF shiftedF (radius R E T)
      (powerExponentData z B (a+c) b) (shiftedData z B a b c) (numerator R c) (a*a) := by
  have ha := h.andE₂.andE₁.andE₁.andE₁
  exact .andI (positive_product _ _ ha ha) (.andI (later_input z R B E T a b c h)
    (.andI (shifted_input z R B E T a b c h) (linear_shift_rate z R B E T a b c h)))

theorem original_Euler_power_shift_exponential_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianRadiusExponentialLipschitzRate.input powerExponentF shiftedF (radius (var 1) (var 3) (var 4))
        (powerExponentData (var 0) (var 2) (var 5+var 7) (var 6))
        (shiftedData (var 0) (var 2) (var 5) (var 6) (var 7)) (numerator (var 1) (var 7)) (var 5*var 5)) :=
  closeUniv 8 (.impI (original_exponential_comparison_input _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerShiftRate
