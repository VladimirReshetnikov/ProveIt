import IPRADerivations.Analysis.Trigonometry.Pi.GaussianPiRationalScale
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling
import IPRADerivations.Analysis.Trigonometry.Hyperbolic.ProductEstimates.GaussianSineProductImaginaryFirstOrderBound

/-!
# Exact finite remainder of the imaginary sine product with its linear factor

The literal scaled product has one remainder from the sine product and
one quadratic cross term from its changing linear coefficient. The
estimate keeps the same finite product cutoff on all legs.
-/

set_option autoImplicit false
set_option maxHeartbeats 750000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolicProductRuleAlgebra

open_ipra
open GaussianPiRationalScale (point point_add point_bound)
open GaussianNameArithmetic (sum_difference)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qadd qmul positive_product qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded qsub qsub_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (product_difference bounded_sum_same)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qmul_associative)
open GaussianSineProductImaginaryFirstOrder (step)
open GaussianSineProductImaginaryFirstOrderBound (derivative_bound derivativeBound finite_error bound)
open GaussianSineProductImaginaryLogDerivative (product derivative)
open GaussianSineProductImaginaryLogDerivativeTail (rational_real_bound)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def value (pi A B N : PTm n) : PTm n := qmul (qmul (point false A B) pi) (product A B N)

def tangent (pi A B N : PTm n) : PTm n := qmul pi (qadd (product A B N) (qmul (point false A B) (derivative A B N)))

def residualBound (R : PTm n) : PTm n := R*bound R+derivativeBound R

ipra_subst residualBound [bound, derivativeBound, GaussianSineProductImaginaryFirstOrderBound.exponent, GaussianSineProductImaginaryFirstOrderBound.forcingBound, GaussianSineProductImaginaryFirstOrderBound.productBound, two]

private theorem rotate_product (a b c : PTm n) : Γ ⊢[PRAAx] qmul (qmul a b) c ≐ qmul b (qmul c a) :=
  (qmul_congr (qmul_commutative a b) (.eqRefl c)).eqTrans
    ((qmul_associative b a c).eqTrans (qmul_congr (.eqRefl b) (qmul_commutative a c)))

private theorem weighted_inner (pi a h p d : PTm n) : Γ ⊢[PRAAx]
    qmul h (qmul pi (qadd p (qmul a d))) ≐ qmul pi (qadd (qmul (qmul h d) a) (qmul p h)) := by
  let w := qadd p (qmul a d)
  have swapped := ((qmul_associative (Γ := Γ) h pi w).eqSymm.eqTrans
    (qmul_congr (qmul_commutative h pi) (.eqRefl w))).eqTrans (qmul_associative pi h w)
  have last := ((qmul_associative (Γ := Γ) h a d).eqSymm.eqTrans
    (qmul_congr (qmul_commutative h a) (.eqRefl d))).eqTrans
      ((qmul_associative a h d).eqTrans (qmul_commutative a (qmul h d)))
  exact swapped.eqTrans (qmul_congr (.eqRefl pi)
    ((GaussianRationalCoefficientScaling.qmul_add h p (qmul a d)).eqTrans
      ((qadd_congr (qmul_commutative h p) last).eqTrans (GaussianRationalLinearProduct.qadd_commutative _ _))))

theorem product_residual (pi a b h p q d : PTm n) (hd : Γ ⊢[PRAAx] qsub b a ≐ h) :
    Γ ⊢[PRAAx] qsub (qsub (qmul (qmul b pi) q) (qmul (qmul a pi) p))
        (qmul h (qmul pi (qadd p (qmul a d)))) ≐
      qmul pi (qadd (qmul (qsub (qsub q p) (qmul h d)) b) (qmul (qmul h h) d)) := by
  let e := qsub q p
  let t := qmul h d
  let u := qmul p h
  have inc := (qsub_congr (rotate_product (Γ := Γ) b pi q) (rotate_product a pi p)).eqTrans
    ((multiplication_difference pi (qmul q b) (qmul p a)).eqTrans
      (qmul_congr (.eqRefl pi) ((product_difference q p b a).eqTrans (qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _) hd)))))
  have sub := (qsub_congr inc (weighted_inner pi a h p d)).eqTrans
    (multiplication_difference pi (qadd (qmul e b) u) (qadd (qmul t a) u))
  have cancel := (sum_difference (Γ := Γ) (qmul e b) (qmul t a) u u).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self u)).eqTrans
      (GaussianRationalLinearProduct.qadd_zero_right _ (qsub_canonical _ _)))
  have correction : Γ ⊢[PRAAx] qmul t (qsub b a) ≐ qmul (qmul h h) d :=
    (qmul_congr (.eqRefl t) hd).eqTrans
      ((qmul_commutative t h).eqTrans (qmul_associative h h d).eqSymm)
  exact sub.eqTrans (qmul_congr (.eqRefl pi)
    (cancel.eqTrans ((product_difference e t b a).eqTrans (qadd_congr (.eqRefl _) correction))))

theorem finite_rate (pi A B C R N P : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] le (A+C) (R*B)) (hpi : Γ ⊢[PRAAx] bounded pi P one) :
    Γ ⊢[PRAAx] distanceBounded (qsub (value pi (A+C) B N) (value pi A B N))
      (qmul (step B C) (tangent pi A B N)) ((P*residualBound R)*(C*C)) (B*B) := by
  let a := point false A B
  let b := point false (A+C) B
  let s := step B C
  let p := product A B N
  let q := product (A+C) B N
  let d := derivative A B N
  let T := B*B
  let E := C*C
  have hA := le_trans (le_add_right A C) h
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ hB hB
  have hb : Γ ⊢[PRAAx] bounded b R one := point_bound false _ _ _ _ hB (le_refl one)
    (le_congr (one_mul _).eqSymm (.eqRefl _) h)
  have hs : Γ ⊢[PRAAx] bounded s C B :=
    rational_real_bound _ _ _ _ hB hB (le_congr (mul_comm _ _) (.eqRefl _) (le_refl _))
  have hd : Γ ⊢[PRAAx] qsub b a ≐ s :=
    (qsub_congr (point_add false A B C hB).eqSymm (.eqRefl a)).eqTrans
      (qadd_sub_cancel a s (GaussianRationalHorner.ofGaussian_canonical _ _ hB))
  have near : Γ ⊢[PRAAx] distanceBounded (qsub q p) (qsub (qadd p (qmul s d)) p)
      (E*bound R+ConciseIPRA.PTm.zero) T :=
    GaussianNamedDifference.difference_distance q (qadd p (qmul s d)) p p _ _ T hT
      (finite_error A B C R N hB h) (GaussianRationalPowerDifference.distance_refl_zero p T hT)
  have delta : Γ ⊢[PRAAx] bounded (qsub (qsub q p) (qmul s d)) (E*bound R) T :=
    distance_congr (.eqRefl _) (qadd_sub_cancel p (qmul s d) (qmul_canonical _ _)) (add_zero _) (.eqRefl _) near
  have clear : Γ ⊢[PRAAx] T*one ≐ T := by ipra_ring
  have first := bound_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] E*bound R*R ≐ E*(R*bound R)) clear
    (bounded_product _ _ _ _ _ _ hT (le_refl one) delta hb)
  have second := bound_congr (.eqRefl _) (.eqRefl _) clear
    (bounded_product _ _ _ _ _ _ hT (le_refl one) (bounded_product _ _ _ _ _ _ hB hB hs hs)
      (derivative_bound A B R N hB hA))
  exact bound_congr (product_residual pi a b s p q d hd).eqSymm
    (by dsimp only [E,residualBound]; ipra_ring) (one_mul T)
    (bounded_product _ _ _ _ _ _ (le_refl one) hT hpi (bounded_sum_same _ _ _ _ _ hT first second))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolicProductRuleAlgebra
