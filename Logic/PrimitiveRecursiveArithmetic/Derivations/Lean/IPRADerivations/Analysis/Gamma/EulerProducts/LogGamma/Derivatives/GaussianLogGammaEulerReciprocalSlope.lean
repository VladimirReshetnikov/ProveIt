import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.Polynomials.RootFinding.FundamentalTheorem.GaussianGeneralFTATelescope
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Names.Differences.GaussianNamedDifference
import IPRADerivations.Analysis.Polynomials.Horner.GaussianReciprocalHorner

/-!
# The finite Euler logarithmic slope on the complex right half-plane

The actual finite slope uses the original real logarithm of the cutoff,
minus the literal Gaussian-rational reciprocal sum. At each positive
row index, its reciprocal differs from the harmonic term by at most
`R/k²`, where `R` bounds the original complex input.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlope

open_ipra
open ComplexLogarithmRemainder (re im normSq normSq_scale normSq_one oneCode scale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianNameReciprocal (inverse_difference)
open GaussianPositiveRationalLogarithm (logF fraction name_regular)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner
  (represents ofGaussian qadd qmul canonical_unique ofGaussian_canonical ofGaussian_represents
    qadd_represents represents_congr represents_rescale positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub qnormSq squaredTolerance)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal
  (normLower reciprocal qone qone_represents_scaled norm_positive inverse_bound reciprocal_identity
    reciprocal_canonical bound_congr bounded_product)
open GaussianRationalSyntheticDivision (qmul_congr qone_canonical)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def shiftedPoint (z k : PTm n) : PTm n := qadd (fraction k one) z

def rowBody : PTm 2 := reciprocal (shiftedPoint (var 1) (var 0))
def reciprocalSum (A B D neg M : PTm n) : PTm n :=
  GaussianRationalFiniteSum.sum rowBody M (argument A B D neg)

def nameF : PR 2 := GaussianNamedDifference.nameF logF constantF
def data (A B D neg N : PTm n) : PTm n :=
  GaussianNamedDifference.data (GaussianPositiveRationalLogarithm.data N one)
    (reciprocalSum A B D neg (succ N))

ipra_subst shiftedPoint [fraction, one]

theorem row_at (z k : PTm n) : Γ ⊢[PRAAx] inst2 rowBody k z ≐ reciprocal (shiftedPoint z k) := by
  simpa only [rowBody, inst2, GaussianRationalReciprocal.subst_reciprocal, subst_shiftedPoint,
    Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one] using
    (Prf.eqRefl (reciprocal (shiftedPoint z k)) : Γ ⊢[PRAAx] _)

theorem regular (A B D neg N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg N) :=
  GaussianNamedDifference.name_regular _ _ _ _ (name_regular N one (.andI hN (le_refl one)))
    (constant_regular _)

private theorem lower_of_representation (q a D k : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hq : Γ ⊢[PRAAx] represents q a D)
    (hr : Γ ⊢[PRAAx] le ((k * D) * (k * D)) (normSq a)) : Γ ⊢[PRAAx] normLower q k :=
  GaussianRationalMetric.comparison_of_cleared (squaredTolerance k one) (qnormSq q)
    (k * k) (normSq a) (one * one) (D * D) (positive_product _ _ (le_refl one) (le_refl one))
    (positive_product _ _ hD hD) (GaussianRationalMetric.squared_tolerance_represents k one (le_refl one))
    (GaussianRationalMetric.qnormSq_represents q a D hD hq)
    (le_congr (by ipra_ring) (by ipra_ring) hr)

private theorem real_lower (k : PTm n) : Γ ⊢[PRAAx] normLower (fraction k one) k := by
  have eq : Γ ⊢[PRAAx] normSq (scale k oneCode) ≐ (k * one) * (k * one) :=
    (normSq_scale k oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring))
  exact lower_of_representation _ _ _ _ (le_refl one) (ofGaussian_represents _ _ (le_refl one))
    (le_congr (.eqRefl _) eq.eqSymm (le_refl _))

private theorem native_shift (A B D neg k : PTm n) : Γ ⊢[PRAAx]
    equal (ComplexLogarithmRemainder.add (scale (k * D) oneCode) (native A B neg))
      (native (A + k * D) B neg) := by
  apply equal_of_values
  · simp only [re_add, re_scale, re_one, native, ComplexLogarithmRemainder.eval_re_code, ZT.toZ_ofNat]
    ipra_simps
    ring
  · simp only [im_add, im_scale, im_one, native, ComplexLogarithmRemainder.eval_im_code]
    ring

theorem shifted_lower (A B D neg k : PTm n) (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source A D neg) :
    Γ ⊢[PRAAx] normLower (shiftedPoint (argument A B D neg) k) k := by
  let z := native A B neg
  let a := native (A + k * D) B neg
  let v := scale k oneCode
  have integer : Γ ⊢[PRAAx] represents (fraction k one) (scale (k * D) oneCode) D := by
    have eq : Γ ⊢[PRAAx] equal (scale D v) (scale (k * D) oneCode) := by
      apply equal_of_values <;> simp only [v, re_scale, im_scale, re_one, im_one] <;> ipra_simps <;> ring
    exact represents_congr (.eqRefl _) eq (one_mul D)
      (represents_rescale (fraction k one) v one D (ofGaussian_represents _ _ (le_refl one)))
  have shift := qadd_represents (fraction k one) (argument A B D neg) (scale (k * D) oneCode) z D
    h.andE₂ integer (ofGaussian_represents z D h.andE₂)
  have rep := represents_congr (.eqRefl _) (native_shift A B D neg k) (.eqRefl D) shift
  have low : Γ ⊢[PRAAx] le ((k * D) * (k * D)) ((A + k * D) * (A + k * D) + B * B) :=
    le_of_eq_add (d := A * A + A * (k * D) + A * (k * D) + B * B) (by ipra_ring)
  exact lower_of_representation (shiftedPoint (argument A B D neg) k) a D k h.andE₂ rep
    (le_congr (.eqRefl _) (native_norm (A + k * D) B neg h.andE₁.andE₂).eqSymm low)

private theorem integer_inverse_distance (a b r s A B : PTm n)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (hB : Γ ⊢[PRAAx] le one B)
    (ha : Γ ⊢[PRAAx] normLower a r) (hb : Γ ⊢[PRAAx] normLower b s)
    (hab : Γ ⊢[PRAAx] distanceBounded a b A B) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal a) (reciprocal b) A (B * (r * s)) := by
  have first := bounded_product (reciprocal a) (qsub b a) one r A B hr hB
    (inverse_bound a r hr ha) (distance_symmetric a b A B hB hab)
  have last := bounded_product (qmul (reciprocal a) (qsub b a)) (reciprocal b) (one * A) (r * B) one s
    (positive_product _ _ hr hB) hs first (inverse_bound b s hs hb)
  exact bound_congr (inverse_difference a b (norm_positive a r hr ha) (norm_positive b s hs hb)).eqSymm
    (by ipra_ring) (by ipra_ring) last

theorem integer_reciprocal (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] reciprocal (fraction k one) ≐ fraction one k := by
  let a := fraction k one
  let b := fraction one k
  let c := reciprocal a
  have prod := GaussianEulerDampedTimeRate.fraction_product k one one k (le_refl one) hk
  have simplify := GaussianCompactRiemannName.fraction_congr (Γ := Γ) (k * one) k (one * k) k
    (by ipra_ring) (one_mul k)
  have unit : Γ ⊢[PRAAx] fraction k k ≐ qone :=
    canonical_unique _ _ _ k (ofGaussian_canonical _ _ hk) qone_canonical hk
      (ofGaussian_represents _ _ hk) (qone_represents_scaled k)
  have ab : Γ ⊢[PRAAx] qmul a b ≐ qone := prod.eqTrans (simplify.eqTrans unit)
  have ac := reciprocal_identity a (norm_positive a k hk (real_lower k))
  have left : Γ ⊢[PRAAx] qmul (qmul b a) c ≐ c :=
    (qmul_congr ((qmul_commutative b a).eqTrans ab) (.eqRefl c)).eqTrans
      ((qmul_commutative qone c).eqTrans (qmul_one_right c (reciprocal_canonical a)))
  have right : Γ ⊢[PRAAx] qmul (qmul b a) c ≐ b :=
    (qmul_associative b a c).eqTrans ((qmul_congr (.eqRefl b) ac).eqTrans
      (qmul_one_right b (ofGaussian_canonical _ _ hk)))
  exact left.eqSymm.eqTrans right

/-- The actual complex reciprocal row is within `R/k²` of the harmonic row. -/
theorem row_tail (A B D neg R k : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal (shiftedPoint (argument A B D neg) k)) (fraction one k) R (k * k) := by
  let z := argument A B D neg
  let a := shiftedPoint z k
  let b := fraction k one
  have hz : Γ ⊢[PRAAx] bounded z R one := by
    have hD := h.andE₁.andE₂
    exact GaussianRationalMetric.bounded_of_cleared z (native A B neg) D R one hD (le_refl one)
      (ofGaussian_represents _ _ hD) (le_congr (by ipra_ring) (by ipra_ring) h.andE₂)
  have hab : Γ ⊢[PRAAx] distanceBounded a b R one := GaussianGeneralFTATelescope.add_increment_distance b z R one hz
  exact distance_congr (.eqRefl _) (integer_reciprocal k hk) (.eqRefl _) (by ipra_ring)
    (integer_inverse_distance a b k k R one hk hk (le_refl one) (shifted_lower A B D neg k h.andE₁)
      (real_lower k) hab)

theorem actual_complex_Euler_logarithmic_slope_row_tail_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶
        distanceBounded (reciprocal (shiftedPoint (argument (var 0) (var 1) (var 2) (var 3)) (var 5)))
          (fraction one (var 5)) (var 4) (var 5 * var 5)) :=
  closeUniv 6 (.impI (.impI (row_tail _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerReciprocalSlope
