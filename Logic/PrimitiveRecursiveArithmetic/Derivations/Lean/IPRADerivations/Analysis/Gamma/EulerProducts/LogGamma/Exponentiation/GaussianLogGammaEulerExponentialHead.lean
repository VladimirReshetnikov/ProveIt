import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Exponentiation.GaussianLogGammaEulerExponentialFold
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Exponentiation.GaussianLogGammaEulerExponentialNumerator

/-!
# Actual finite Euler log-Gamma and reciprocal Gamma heads

The exponential of the negative normalized log-Gamma head is the
original reciprocal Euler approximant. The denominator exponential
recovers the actual numerical Euler polynomial, and the other factor
keeps the original mesh program for the negative power of the cutoff.
The exact normalization transports the identity to the original head
with the factorial.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialHead

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaFiniteApproximantName (qF qData logExponentF logExponentData log_exponent_regular exponentialInputData exponential_input)
open GaussianLogGammaEulerHead (argument rowData productF productData)
open GaussianLogGammaEulerNormalizedHead (denominatorF denominatorData denominator_regular product_regular)
open GaussianLogGammaEulerExponentialFold (prefixF prefixData prefix_regular)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianNameArithmetic (addF addData multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameRingLaws (negativeF negativeData negative_fast negative_sample_error negative_equivalent)
open GaussianNamedDiagonalRate (cross_of_diagonal_rate diagonalRate)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same distance_symmetric reversed_difference)
open GaussianRationalMetric (qnegative qnegative_canonical qsub distanceBounded)
open GaussianRationalHorner (qzero)
open GaussianRationalSyntheticDivision (qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "diffF" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data

private theorem negate_difference_at (f g : PR 2) (x y p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (negativeF (diffF f g)) p (negativeData (dd x y)))
      (ap2 (diffF g f) p (dd y x)) (num 15) (unit p) := by
  let a := ap2 f p x
  let b := ap2 g p y
  let s := ap2 (diffF f g) p (dd x y)
  have hp := unit_positive (Γ := Γ) p
  have d := GaussianNamedDifference.name_regular f g x y hf hg
  have minus := distance_congr (.eqRefl _) (qzero_add _ (qnegative_canonical s)) (.eqRefl _) (.eqRefl _)
    (negative_sample_error (diffF f g) (dd x y) p d)
  have before := GaussianNamedDifference.negative_distance s (qsub a b) _ _ hp
    (GaussianNamedDifference.sample_error f g x y p hf hg)
  have reverse := distance_congr (.eqRefl _) (reversed_difference a b) (.eqRefl _) (.eqRefl _) before
  have last := distance_symmetric _ _ _ _ hp (GaussianNamedDifference.sample_error g f y x p hg hf)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp (distance_triangle_same _ _ _ _ _ _ hp minus reverse) last)

private theorem negate_difference (f g : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent (negativeF (diffF f g)) (diffF g f) (negativeData (dd x y)) (dd y x) := by
  refine cross_of_diagonal_rate _ _ _ _ (num 15)
    (negative_fast _ _ (GaussianNamedDifference.name_regular f g x y hf hg))
    (GaussianNamedDifference.name_regular g f y x hg hf) (.allI ?_)
  have hfx : Γ.map Fm.shift ⊢[PRAAx] pointCN f (Syn.shift x) := by simpa [Fm.shift,Syn.shift] using hf.shift
  have hgy : Γ.map Fm.shift ⊢[PRAAx] pointCN g (Syn.shift y) := by simpa [Fm.shift,Syn.shift] using hg.shift
  simpa [diagonalRate,Syn.shift] using negate_difference_at f g (Syn.shift x) (Syn.shift y) (var 0) hfx hgy

theorem denominator_exponential (A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] crossEquivalent (E denominatorF) constantF
      (exponentialInputData denominatorF (denominatorData A B D neg N))
      (GaussianGammaEulerHead.run (native A B neg) D N) := by
  let G := GaussianLogGammaEulerFactorSum.residualF
  let x := ld A B D neg
  let y := GaussianNamedFiniteSumFamily.data N (rowData A B D neg)
  let z := native A B neg
  let a := argument A B D neg
  let b := GaussianGammaEulerHead.product z D N
  let X := exponentialInputData L x
  let Y := prefixData N (rowData A B D neg)
  have hx := exponential_input L x (GaussianRightHalfPlaneLogarithm.regular A B D neg h.andE₁)
  have hy := exponential_input G y (GaussianNamedFiniteSumFamily.regular _ _ _ _
    (GaussianLogGammaEulerFactorSum.residual_rows A B D neg N h.andE₁))
  have hz := exponential_input denominatorF (denominatorData A B D neg N) (denominator_regular A B D neg N h.andE₁)
  have addition := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent L G denominatorF
    _ _ _ x y (denominatorData A B D neg N) hx hy hz (cross_refl _ _ hz.andE₁)
  have replace := multiply_cross (E L) constantF prefixF constantF X a Y b
    (GaussianRadiusExponentialName.name_regular _ _ _ hx) (constant_regular a)
    (prefix_regular A B D neg N h.andE₁) (constant_regular b)
    (GaussianRightHalfPlaneLogarithmExponential.recovery A B D neg h.andE₁)
    (GaussianLogGammaEulerExponentialFold.exponential_product A B D neg R N h)
  have close := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross (Γ := Γ) a b)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (GaussianGammaEulerHead.program_at z D N).eqSymm)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ addition) (cross_trans _ _ _ _ _ _ replace close)

def reciprocalF : PR 2 := E (negativeF GaussianLogGammaEulerNormalizedHead.nameF)
def reciprocalData (A B D neg N : PTm n) : PTm n :=
  exponentialInputData (negativeF GaussianLogGammaEulerNormalizedHead.nameF)
    (negativeData (GaussianLogGammaEulerNormalizedHead.data A B D neg N))

theorem reciprocal_equivalent (A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent reciprocalF qF (reciprocalData A B D neg N) (qData (native A B neg) D N) := by
  let x := productData A B D neg N
  let y := denominatorData A B D neg N
  let z := native A B neg
  let s := dd x y
  let t := dd y x
  let g := diffF denominatorF productF
  let f := negativeF GaussianLogGammaEulerNormalizedHead.nameF
  let e := negativeF productF
  let a := exponentialInputData denominatorF y
  let b := exponentialInputData e (negativeData x)
  let c := exponentialInputData logExponentF (logExponentData z D N)
  have hx := product_regular A B D neg N hN
  have hy := denominator_regular A B D neg N h.andE₁
  have ht := GaussianNamedDifference.name_regular denominatorF productF y x hy hx
  have hl := negative_fast _ _ (GaussianNamedDifference.name_regular productF denominatorF x y hx hy)
  have hn := exponential_input e (negativeData x) (negative_fast _ _ hx)
  have hd := exponential_input denominatorF y hy
  have swap := GaussianExponentialRadiusIndependence.independent_radii_proper f g _ _ (negativeData s) t
    (exponential_input _ _ hl) (exponential_input _ _ ht) (negate_difference productF denominatorF x y hx hy)
  have addition := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent denominatorF e g
    _ _ _ y (negativeData x) t hd hn (exponential_input _ _ ht) (cross_refl _ _ ht)
  have replace := multiply_cross (E denominatorF) constantF (E e) (E logExponentF) a
    (GaussianGammaEulerHead.run z D N) b c (GaussianRadiusExponentialName.name_regular _ _ _ hd) (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ hn)
    (GaussianRadiusExponentialName.name_regular _ _ _ (exponential_input _ _ (log_exponent_regular z D N hN)))
    (denominator_exponential A B D neg R N h) (GaussianLogGammaEulerExponentialNumerator.negative_exponential A B D neg N hN)
  exact cross_trans _ _ _ _ _ _ swap (cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ addition) replace)

theorem original_reciprocal_equivalent (A B D neg R N : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (E (negativeF GaussianLogGammaEulerHead.nameF)) qF
      (exponentialInputData (negativeF GaussianLogGammaEulerHead.nameF) (negativeData (GaussianLogGammaEulerHead.data A B D neg N)))
      (qData (native A B neg) D N) := by
  let f := GaussianLogGammaEulerHead.nameF
  let g := GaussianLogGammaEulerNormalizedHead.nameF
  let x := GaussianLogGammaEulerHead.data A B D neg N
  let y := GaussianLogGammaEulerNormalizedHead.data A B D neg N
  have hf := GaussianLogGammaEulerHead.regular A B D neg N h.andE₁ hN
  have hg := GaussianLogGammaEulerNormalizedHead.regular A B D neg N h.andE₁ hN
  have eq := GaussianLogGammaEulerNormalizedHead.equivalent A B D neg N h.andE₁ hN
  have n := negative_equivalent f g x y hf hg (cross_to_diagonal _ _ _ _ eq)
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper
    (negativeF f) (negativeF g) _ _ (negativeData x) (negativeData y)
    (exponential_input _ _ (negative_fast _ _ hf)) (exponential_input _ _ (negative_fast _ _ hg)) n
  exact cross_trans _ _ _ _ _ _ exp (reciprocal_equivalent A B D neg R N h hN)

theorem actual_original_log_Gamma_Euler_head_reciprocal_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶
        crossEquivalent (E (negativeF GaussianLogGammaEulerHead.nameF)) qF
          (exponentialInputData (negativeF GaussianLogGammaEulerHead.nameF)
            (negativeData (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 5))))
          (qData (native (var 0) (var 1) (var 3)) (var 2) (var 5))) :=
  closeUniv 6 (.impI (.impI (original_reciprocal_equivalent _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerExponentialHead
