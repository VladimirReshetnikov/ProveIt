import IPRADerivations.Analysis.Gamma.HalfInteger.SquareRoots.GaussianGammaHalfPositiveRoot
import IPRADerivations.Analysis.Gamma.HalfInteger.SquareRoots.GaussianGammaHalfSqrtBrackets

/-!
# Original Gamma at one half is the bounded-search square root of π

The square-root program reads only the original arctangent quadrature.
It computes the lower endpoint selected by bounded rational search at
precision p+2 from the quadrature at precision 2(p+2). The Gamma value
is used in the proof of accuracy, with an independent computed query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfSqrtPi

open_ipra
open LeanProofs.IPRA.Foundations.SquareRootRelationalCandidates (candidate)
open GaussianGammaHalfSquareLimit (gammaHalf gamma_regular)
open GaussianGammaHalfPiName (meshAt clearing unit_mono)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianGammaRealValues (axisF)
open GaussianGammaHalfPositiveRoot (half_axis lower_at)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans cross_symm point_at)
open GaussianEuclideanDistanceName (pointCN)
open RationalSupMetric (denominatorOf numeratorOf)
open GaussianPositiveRealArithmetic (sign numerator)
open Products (fact)
open GaussianGammaHalfPositiveRoot renaming shift_gammaHalf → shift_half

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def rootClock (p : PTm n) : PTm n := succ (succ p)
def piClock (p : PTm n) : PTm n := p+p
def piNumerator (p : PTm n) : PTm n := num 4*BaselQuadrature.Q (meshAt (piClock p)) (clearing (piClock p))
def piDenominator (p : PTm n) : PTm n := fact (clearing (piClock p))
def rootPoint (p : PTm n) : PTm n := fraction (candidate (piNumerator p) (piDenominator p) p) (unit p)
def nameF : PR 2 := PTm.toPR (rootPoint (rootClock (var 0)) : PTm 2)

private theorem pi_denominator_positive (p : PTm n) : Γ ⊢[PRAAx] le one (piDenominator p) :=
  GaussianGammaHalfRisingFactorial.factorial_positive _

private theorem root_point_subst {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) :
    Syn.subst σ (rootPoint p) = rootPoint (Syn.subst σ p) := by
  simp [rootPoint,piNumerator,piDenominator,piClock,meshAt,clearing,
    GaussianGammaHalfPiName.orderAt,GaussianGammaHalfPiName.orderIndex,GaussianGammaHalfPiName.meshIndex,
    WallisFinite.Dm,Products.fact]

theorem sample_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 nameF p x ≐ rootPoint (rootClock p) := by
  simpa only [nameF,ap2,root_point_subst,rootClock,ConciseIPRA.PTm.subst_succ,Syn.subst_var,
    Matrix.cons_val_zero] using
    toPR_eq (Γ := Γ) (rootPoint (rootClock (var 0)) : PTm 2) ![p,x]

abbrev realF : PR 2 := axisF gammaF
def squareCost : PTm n := GaussianNameArithmetic.multiplyModulus realF realF gammaHalf gammaHalf+one
def gammaClock (p : PTm n) : PTm n := GaussianFastValueCut.exponent (squareCost+num 18+one) (piClock p)
def scalar (t : PTm n) : PTm n := fstT (ap2 gammaF t gammaHalf)

private theorem axis_regular : Γ ⊢[PRAAx] pointCN realF (gammaHalf : PTm n) :=
  GaussianGammaRealValues.axis_regular _ _ gamma_regular

private theorem axis_square_is_pi (x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianGammaHalfEulerSquare.squareF realF) GaussianGammaHalfPiName.nameF
      (GaussianGammaHalfEulerSquare.squareData realF gammaHalf) x := by
  have axis := cross_symm _ _ _ _ (half_axis (Γ := Γ))
  have square := GaussianGammaAdjacentCutoff.multiply_cross realF gammaF realF gammaF
    gammaHalf gammaHalf gammaHalf gammaHalf axis_regular gamma_regular axis_regular gamma_regular axis axis
  exact cross_trans _ _ _ _ _ _ square (GaussianGammaHalfSquareLimit.original_half_square_is_pi x)

private theorem clock_budget (p : PTm n) :
    Γ ⊢[PRAAx] le ((squareCost+num 18+one)*unit (piClock p)) (unit (gammaClock p)) :=
  GaussianFastValueCut.query_budget _ _

private theorem clock_later (p : PTm n) : Γ ⊢[PRAAx] le p (gammaClock p) :=
  le_trans (le_add_right p p) (le_add_right _ _)

private theorem late_sign (t : PTm n) (ht : Γ ⊢[PRAAx] le (num 18) (unit t)) :
    Γ ⊢[PRAAx] sign (scalar t) := by
  let U := unit t
  let b := denominatorOf (scalar t)
  let a := numeratorOf (scalar t)
  let c : PTm n := num 18
  have hC : Γ ⊢[PRAAx] le one c := by unfold c; ipra_le 17
  let l := ZT.ofNat (U*b)*ZT.ofNat one
  let r := ZT.ofNat (U*c)*a+ZT.ofNat (one*c*b)
  have signed : Γ ⊢[PRAAx] zle l r :=
    RationalUpperRepresentation.upper_from_representations _ _ c b one U (ZT.ofNat one) a
      (GaussianEuclideanDistanceName.fraction_represents one c hC) (RationalRepresentations.represents_self _) (lower_at t)
  have e := zle_toZ signed
  have clockOrder : Γ ⊢[PRAAx] le c U := ht
  have ec := natEq (eq_add_of_le clockOrder)
  have ordered : Γ ⊢[PRAAx] le ((U*c)*a.neg) ((U*c)*a.pos) := by
    apply le_of_eq_add (d := PolynomialBisection.slack l r+b*monus U c)
    apply deriveNat
    dsimp only [l,r] at e ⊢
    simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at e
    unfold ZT.toZ at e
    unfold PolynomialBisection.slack
    ipra_simps
    linear_combination -e+𝔞 b*ec
  exact RationalValueBounds.positive_cancel (positive_product _ _ (unit_positive t) hC) ordered

private theorem axis_fraction (t : PTm n) (ht : Γ ⊢[PRAAx] le (num 18) (unit t)) :
    Γ ⊢[PRAAx] ap2 realF t gammaHalf ≐ fraction (numerator (scalar t)) (denominatorOf (scalar t)) := by
  let s := scalar t
  let a := numerator s
  let b := denominatorOf s
  have hb : Γ ⊢[PRAAx] le one b := RationalArgmin.denominator_positive _
  have rep := GaussianPositiveRealArithmetic.natural_representation s (late_sign t ht)
  have emb := RationalGaussianEmbedding.embed_from_representation _ _ _ rep
  have frac := GaussianRationalHorner.ofGaussian_represents
    (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b hb
  have same := GaussianRationalHorner.represents_congr (.eqRefl _)
    (GaussianCompactLogarithmBounds.natural_native a) (.eqRefl _) frac
  exact (GaussianGammaRealValues.axis_sample_at gammaF t gammaHalf).eqTrans
    (GaussianRationalHorner.canonical_unique _ _ _ b (RationalGaussianEmbedding.embed_canonical s)
      (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hb emb same)

private theorem unit_pi_precision (p : PTm n) : Γ ⊢[PRAAx] unit (piClock p) ≐ unit p*unit p :=
  pw_add two p p

theorem scheduled_axis_to_root (p : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 realF (gammaClock p) gammaHalf) (rootPoint p) (num 3) (unit p) := by
  let t := gammaClock p
  let U := unit t
  let P := unit (piClock p)
  let C : PTm n := squareCost
  let a := numerator (scalar t)
  let b := denominatorOf (scalar t)
  let Z := ap2 realF t gammaHalf
  let X := ap2 (GaussianGammaHalfEulerSquare.squareF realF) t (GaussianGammaHalfEulerSquare.squareData realF gammaHalf)
  let Y := ap2 GaussianGammaHalfPiName.nameF (piClock p) (zero : PTm n)
  have time : Γ ⊢[PRAAx] le ((C+num 18+one)*P) U := clock_budget p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive t
  have hP : Γ ⊢[PRAAx] le one P := unit_positive (piClock p)
  have D := positive_product (Γ := Γ) _ _ hU hP
  have late : Γ ⊢[PRAAx] le (num 18) U := le_trans
    (by ipra_le 𝔞 (num 18 : PTm n) * sl hP + 𝔞 C * 𝔞 P + 𝔞 P) time
  have g : Γ ⊢[PRAAx] Z ≐ fraction a b := axis_fraction t late
  have hb : Γ ⊢[PRAAx] le one b := RationalArgmin.denominator_positive _
  have f : Γ ⊢[PRAAx] qmul Z Z ≐ fraction (a*a) (b*b) :=
    (GaussianRationalSyntheticDivision.qmul_congr g g).eqTrans
      (GaussianEulerDampedTimeRate.fraction_product a b a b hb hb)
  have err : Γ ⊢[PRAAx] distanceBounded X (qmul Z Z) C U :=
    GaussianNameRingLaws.multiply_sample_error realF realF gammaHalf gammaHalf t axis_regular axis_regular
  have first : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) X (C*P) (U*P) :=
    distance_radius_mono _ _ _ _ _ _ hU D (by ipra_le 0)
      (distance_congr (.eqRefl _) f (.eqRefl _) (.eqRefl _) err |> distance_symmetric _ _ _ _ hU)
  have second : Γ ⊢[PRAAx] distanceBounded X Y (U+P) (U*P) :=
    cross_at _ _ _ _ t (piClock p) (axis_square_is_pi _)
  have combined := distance_triangle_same _ _ _ _ _ _ D first second
  have slack : Γ ⊢[PRAAx] le (C*P+(U+P)) (two*U) := by
    have step : Γ ⊢[PRAAx] le ((C+one)*P) U :=
      le_trans (by ipra_le 𝔞 (num 18 : PTm n) * 𝔞 P) time
    ipra_le sl step
  have rescaled : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) Y (two*two) P :=
    distance_radius_mono _ _ _ _ _ _ D hP (by ipra_le 𝔞 P * sl slack + 2 * 𝔞 U * 𝔞 P) combined
  have reflected : Γ ⊢[PRAAx] Y ≐ fraction (piNumerator p) (piDenominator p) :=
    GaussianGammaHalfPiName.sample_at (piClock p) zero
  have sq : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) (fraction (piNumerator p) (piDenominator p))
      (two*two) (unit p*unit p) :=
    distance_congr (.eqRefl _) reflected (.eqRefl _) (unit_pi_precision p) rescaled
  have comp := GaussianGammaHalfSqrtBrackets.bounded_root_close a b (piNumerator p) (piDenominator p)
    p two hb (pi_denominator_positive p) sq
  exact distance_congr g.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) comp

private theorem unit_root_clock (p : PTm n) : Γ ⊢[PRAAx] unit (rootClock p) ≐ num 4*unit p := by
  unfold rootClock unit
  exact (pw_succ two (succ p)).eqTrans ((congrMul (pw_succ two p) (.eqRefl _)).eqTrans (by ipra_ring))

theorem axis_to_sqrt_at (p q x : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (ap2 realF p gammaHalf) (ap2 nameF q x)
      (unit p+unit q) (unit p*unit q) := by
  let P := unit p
  let Q := unit q
  let r := rootClock q
  let D := unit r
  let t := gammaClock r
  let T := unit t
  let X := ap2 realF p gammaHalf
  let Y := ap2 realF t gammaHalf
  let Z := rootPoint r
  have hP : Γ ⊢[PRAAx] le one P := unit_positive p
  have hQ : Γ ⊢[PRAAx] le one Q := unit_positive q
  have hD : Γ ⊢[PRAAx] le one D := unit_positive r
  have hT : Γ ⊢[PRAAx] le one T := unit_positive t
  have later : Γ ⊢[PRAAx] le D T := unit_mono r t (clock_later r)
  have pd := positive_product (Γ := Γ) _ _ hP hD
  have first : Γ ⊢[PRAAx] distanceBounded X Y (P+D) (P*D) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hP hT) pd (by ipra_le 𝔞 P^2*sl later)
      (point_at realF gammaHalf p t axis_regular)
  have second : Γ ⊢[PRAAx] distanceBounded Y Z (num 3*P) (P*D) :=
    distance_radius_mono _ _ _ _ _ _ hD pd (by ipra_le 0) (scheduled_axis_to_root r)
  have total := distance_triangle_same X Y Z (P+D) (num 3*P) (P*D) pd first second
  have narrowed : Γ ⊢[PRAAx] distanceBounded X Z (P+Q) (P*Q) :=
    distance_radius_mono _ _ _ _ _ _ pd (positive_product _ _ hP hQ)
      (by ipra_le 0 with (𝔞 P)^2*natEq (unit_root_clock (Γ := Γ) q)) total
  exact distance_congr (.eqRefl _) (sample_at q x).eqSymm (.eqRefl _) (.eqRefl _) narrowed

theorem axis_cross_sqrt (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent realF nameF gammaHalf x := by
  refine .allI (.allI ?_)
  change (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] distanceBounded
    (ap2 realF (var 1) (Syn.shift (Syn.shift (gammaHalf : PTm n))))
    (ap2 nameF (var 0) (Syn.shift (Syn.shift x)))
    (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0))
  rw [shift_half,shift_half]
  exact axis_to_sqrt_at (var 1) (var 0) (Syn.shift (Syn.shift x))

theorem original_half_is_sqrt_pi (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent gammaF nameF gammaHalf x :=
  cross_trans _ _ _ _ _ _ half_axis (axis_cross_sqrt x)

theorem original_Gamma_half_is_bounded_sqrt_Pi_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (crossEquivalent gammaF nameF gammaHalf (var 0)) :=
  closeUniv 1 (original_half_is_sqrt_pi _)

end LeanProofs.IPRA.Analysis.GaussianGammaHalfSqrtPi
