import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionCayleyMargins
import IPRADerivations.Analysis.Trigonometry.Arctangent.Cayley.NamedValues.GaussianArctangentNamedCayleyTrig
import IPRADerivations.Analysis.Trigonometry.Arctangent.DivisionAngles.GaussianArctangentDivisionSinePositive
import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff

/-!
# Separation of the original squared sine names

Independent queries to the original squared sine programs are compared
through a common cofinal Cayley observation. Its positive rational gap
survives exact removal of the temporary observation slack.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000

namespace LeanProofs.IPRA.Analysis.GaussianArctangentDivisionSineSeparation

open_ipra
open GaussianArctangentDivisionAngles (nameF data modulus odd_source interval_input imaginary_samples exponential_input)
open GaussianArctangentDivisionSinePositive (exactSineData)
open GaussianArctangentDivisionAngleResidual (inverseF inverseData sineSample)
open GaussianArctangentDivisionCayleyMargins (squareSample squared_sine_gap_at)
open GaussianArctangentCayleySquareGap (separationDenominator)
open GaussianArctangentCayleyProjections (sineProjectionF)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open GaussianNamedSineFromExponential (sineF sine_regular sine_proper)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open RationalCubeMidpoint (fraction)
open RationalArithmetic (add)
open RationalValueBounds (upper radius radius_mono radius_triangle radius_symmetric upper_of_radius
  upper_of_order upper_order_right upper_triangle upper_mono upper_congr crossLeft)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def squareF : PR 2 := multiplyF (sineF nameF) (sineF nameF)
def squareData (k J z : PTm n) : PTm n :=
  multiplyData (sineF nameF) (sineF nameF) (exactSineData k (modulus J) z) (exactSineData k (modulus J) z)
def squareOrdinate (p k J z : PTm n) : PTm n := fstT (ap2 squareF p (squareData k J z))
def gap (J : PTm n) : PTm n := fraction one (separationDenominator (num 4*modulus J))
def cayleyClock (t : PTm n) : PTm n := GaussianFastValueCut.exponent GaussianArctangentNamedCayley.modulus t

private def projectedData (k J z : PTm n) : PTm n := GaussianArctangentNamedCayley.data (inverseData k J z)
private def squareBudget (k J z : PTm n) : PTm n :=
  multiplyModulus (sineProjectionF inverseF) (sineProjectionF inverseF) (projectedData k J z) (projectedData k J z)+two

private theorem square_radius (p t k J z : PTm n) (hJ : Γ ⊢[PRAAx] le k J) :
    Γ ⊢[PRAAx] radius (squareOrdinate p k J z) (squareSample (cayleyClock t) k J z)
      (unit t+squareBudget k J z*unit p) (unit p*unit t) := by
  let m := modulus J
  let X := data k m z
  let Y := inverseData k J z
  let F := GaussianArctangentInverseCorrectness.roundTripF nameF
  let G := sineProjectionF inverseF
  let a := exactSineData k m z
  let b := projectedData k J z
  let hs := odd_source k J hJ
  have hinterval := interval_input k m z hs
  have hi := GaussianArctangentNamedInverse.name_regular nameF X z hinterval
  have ha := exponential_input k m z hs
  have hb := GaussianArctangentNamedCayley.exp_input inverseF Y hi
  have he := GaussianArctangentInverseCorrectness.imaginary_right_inverse nameF X z hinterval
    (imaginary_samples k m z hs.andE₁)
  have sf : Γ ⊢[PRAAx] crossEquivalent (sineF nameF) (sineF F) a (GaussianNamedSineFromExponential.sineData F two Y) :=
    sine_proper _ _ _ _ _ _ ha hb (cross_symm _ _ _ _ he)
  have proj := GaussianArctangentNamedCayleyTrig.sine_cross inverseF Y hi
  have s : Γ ⊢[PRAAx] crossEquivalent (sineF nameF) G a b :=
    cross_trans _ _ _ _ _ _ sf proj
  have ra := sine_regular _ _ _ ha
  have rb := GaussianImaginaryCoordinateName.name_regular _ _ (GaussianArctangentNamedCayley.name_regular inverseF Y hi)
  have product := GaussianGammaAdjacentCutoff.multiply_cross _ _ _ _ _ _ _ _ ra rb ra rb s s
  have hU := unit_positive (Γ := Γ) p
  have hT := unit_positive (Γ := Γ) t
  have hUT := positive_product _ _ hU hT
  have step := scalar_coordinate_distance _ _ _ _ hUT (cross_at _ _ _ _ p t product)
  have rep : Γ ⊢[PRAAx] ap2 G t b ≐ sineSample (cayleyClock t) k J z :=
    GaussianArctangentCayleyProjections.sine_sample_at inverseF t Y
  have sample := GaussianNameRingLaws.multiply_sample_error G G b b t rb rb
  have readback := scalar_coordinate_distance _ _ _ _ hT
    (distance_congr (.eqRefl _) (qmul_congr rep rep) (.eqRefl _) (.eqRefl _) sample)
  have joined := radius_triangle _ _ _ _ _ _ _ step readback
  exact radius_mono _ _ _ _ _ _ (positive_product _ _ hUT hT) joined
    (le_of_eq_add (d := zero) (by unfold squareBudget; dsimp only [G,b]; ipra_ring))

private theorem fine_at (t J : PTm n)
    (h : Γ ⊢[PRAAx] le (GaussianFastValueCut.normalizer (num 28*modulus J)) t) :
    Γ ⊢[PRAAx] le (num 28*modulus J) (unit (GaussianArctangentDivisionCayleyMargins.precision (cayleyClock t))) := by
  let q := cayleyClock t
  let s := GaussianArctangentNamedCayley.queryPrecision q
  have h₁ : Γ ⊢[PRAAx] le t q := le_add_right _ _
  have h₂ : Γ ⊢[PRAAx] le q s := le_trans (le_add_right _ _) (le_add_right _ _)
  have h₃ : Γ ⊢[PRAAx] le s (GaussianArctangentNamedExtension.clock s) := le_add_right _ _
  have h₄ := GaussianArctangentNamedInverse.precision_later (Γ := Γ) (GaussianArctangentNamedExtension.clock s)
  have ht := le_trans h (le_trans h₁ (le_trans h₂ (le_trans h₃ h₄)))
  exact le_trans (GaussianFastValueCut.normalizer_budget _) (GaussianExponentialReference.unit_monotone ht)

private theorem cofinal_gap (p q t k l J z : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkl : Γ ⊢[PRAAx] lt k l) (hl : Γ ⊢[PRAAx] le l J)
    (h : Γ ⊢[PRAAx] le (GaussianFastValueCut.normalizer (num 28*modulus J)) t) :
    Γ ⊢[PRAAx] GaussianNamedRealOrderTransport.upperSlack (add (squareOrdinate p k J z) (gap J))
      (squareOrdinate q l J z) (unit p+unit q) (unit p*unit q) (squareBudget k J z+squareBudget l J z) t := by
  let a := squareOrdinate p k J z
  let b := squareOrdinate q l J z
  let P := unit p
  let Q := unit q
  let T := unit t
  let E := squareBudget k J z
  let F := squareBudget l J z
  let d := gap J
  let u := squareSample (cayleyClock t) k J z
  let v := squareSample (cayleyClock t) l J z
  have hP := unit_positive (Γ := Γ) p
  have hQ := unit_positive (Γ := Γ) q
  have hT := unit_positive (Γ := Γ) t
  have kJ := le_trans (le_of_lt hkl) hl
  have left : Γ ⊢[PRAAx] upper (add a d) (add u d) (T+E*P) (P*T) :=
    RationalUpperAddition.add_upper_order_right (upper_of_radius _ _ _ _ (square_radius p t k J z kJ))
      (RationalArgmin.reflexive d)
  have mid : Γ ⊢[PRAAx] upper (add a d) v (T+E*P) (P*T) :=
    upper_order_right _ _ _ _ _ left (squared_sine_gap_at (cayleyClock t) k l J z hk hkl hl (fine_at t J h))
  have right : Γ ⊢[PRAAx] upper v b (T+F*Q) (Q*T) :=
    upper_of_radius _ _ _ _ (radius_symmetric _ _ _ _ (square_radius q t l J z hl))
  exact upper_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ hP hT) (positive_product _ _ hQ hT))
    (upper_triangle _ _ _ _ _ _ _ mid right) (le_of_eq_add (d := zero) (by ipra_ring))

theorem named_squared_sine_gap_at (p q k l J z : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hkl : Γ ⊢[PRAAx] lt k l) (hl : Γ ⊢[PRAAx] le l J) :
    Γ ⊢[PRAAx] upper (add (squareOrdinate p k J z) (gap J)) (squareOrdinate q l J z)
      (unit p+unit q) (unit p*unit q) := by
  let a := add (squareOrdinate p k J z) (gap J)
  let b := squareOrdinate q l J z
  let A := unit p+unit q
  let B := unit p*unit q
  let C := squareBudget k J z+squareBudget l J z
  let s := GaussianNamedRealOrderTransport.precision a b B C
  let N := GaussianFastValueCut.normalizer (num 28*modulus J)
  let t := s+N
  have small : Γ ⊢[PRAAx] lt s (unit t) :=
    le_trans (LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (le_refl two) s)
      (GaussianExponentialReference.unit_monotone (le_add_right s N))
  have joined : Γ ⊢[PRAAx] GaussianNamedRealOrderTransport.upperSlack a b A B C t :=
    cofinal_gap p q t k l J z hk hkl hl (le_add_left N s)
  change Γ ⊢[PRAAx] upper a b A B
  apply GapRemoval.gap_of small
  change Γ ⊢[PRAAx] le ((B*crossLeft a b)*unit t)
    ((B*crossLeft b a+A*denominatorOf a*denominatorOf b)*unit t+s)
  exact le_congr (by ipra_ring) (by dsimp only [s,GaussianNamedRealOrderTransport.precision]; ipra_ring) joined

theorem actual_division_sine_square_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (le one (var 2) ⟶ lt (var 2) (var 3) ⟶ le (var 3) (var 4) ⟶
      upper (add (squareOrdinate (var 0) (var 2) (var 4) (var 5)) (gap (var 4)))
        (squareOrdinate (var 1) (var 3) (var 4) (var 5)) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (.impI (.impI (named_squared_sine_gap_at _ _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianArctangentDivisionSineSeparation
