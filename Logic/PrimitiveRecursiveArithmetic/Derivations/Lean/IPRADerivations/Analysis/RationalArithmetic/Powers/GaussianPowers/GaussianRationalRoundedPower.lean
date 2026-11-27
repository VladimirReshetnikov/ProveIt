import IPRADerivations.Analysis.RationalArithmetic.Powers.GaussianPowers.GaussianRationalPowerDifference
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder

/-!
# Actual rounded integer powers on the rational unit circle

For the numerical identity P=k*a+r, the actual output w=q^a satisfies
distance(w^k,q^P)<=r*A/B whenever q is unit and distance(q,1)<=A/B.
Every exponent, radius and original code is internal. The proof derives
the actual power-one invariant, factors the true product difference, and
uses the checked unit-disk runtime power bound. It assumes no output law,
canonical original code, nonzero exponent, or successful rounded search.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRoundedPower

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (qmul qadd qzero)
open LeanProofs.IPRA.Analysis.GaussianRationalSyntheticDivision
  (qone qmul_congr qadd_congr qmul_zero_left qzero_add qone_canonical)
open LeanProofs.IPRA.Analysis.GaussianRationalReciprocal
  (power powerF power_zero power_succ power_canonical bound_congr)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qsub qnormSq bounded distanceBounded)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Analysis.GaussianRationalPowerAlgebra
  (power_add power_composition unit_power unit_bounded norm_one)
open LeanProofs.IPRA.Analysis.GaussianRationalDistanceOrder (distance_congr distance_symmetric)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def oneLaw (j : PTm n) : Fm PTm n := power qone j ≐ qone
ipra_subst oneLaw

/-- The constant unit is preserved by the actual numerical power loop. -/
theorem qone_power (j : PTm n) : Γ ⊢[PRAAx] power qone j ≐ qone := by
  have all : Γ ⊢[PRAAx] .all (oneLaw (var 0)) := by
    ipra_qfind [subst_oneLaw]
    · exact power_zero qone
    · exact (power_succ qone (var 0)).eqTrans
        ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans
          (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
  change Γ ⊢[PRAAx] oneLaw j
  simpa only [subst_oneLaw,Syn.subst_var,Syn.inst_zero] using all.allE j

/-- This literal normalized identity inherits its finite-denominator
representation proof from product_difference; no raw unit cancellation
or supplied distributive law is used. -/
theorem multiplication_difference (t u v : PTm n) : Γ ⊢[PRAAx]
    qsub (qmul t u) (qmul t v) ≐ qmul t (qsub u v) :=
  (GaussianRationalPowerDifference.product_difference t t u v).eqTrans
    ((qadd_congr (qmul_congr (GaussianCoefficientNormOrder.qsub_self t) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((qadd_congr (qmul_zero_left u) (.eqRefl _)).eqTrans
        (qzero_add _ (GaussianRationalHorner.qmul_canonical _ _))))

/-- Left multiplication scales a distance bound by the factor's norm bound. -/
theorem distance_mul_left {t u v C D A B : PTm n}
    (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] bounded t C D) (hd : Γ ⊢[PRAAx] distanceBounded u v A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul t u) (qmul t v) (C*A) (D*B) :=
  bound_congr (multiplication_difference t u v).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product t (qsub u v) C D A B hD hB ht hd)

/-- A unit-denominator factor bound preserves the distance denominator. -/
theorem distance_mul_left_one {t u v C A B : PTm n}
    (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] bounded t C one) (hd : Γ ⊢[PRAAx] distanceBounded u v A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul t u) (qmul t v) (C*A) B :=
  bound_congr (multiplication_difference t u v).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalReciprocal.bounded_product_one_left hB ht hd)

theorem multiply_distance_bound (t u v A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (ht : Γ ⊢[PRAAx] bounded t one one) (hd : Γ ⊢[PRAAx] distanceBounded u v A B) :
    Γ ⊢[PRAAx] distanceBounded (qmul t u) (qmul t v) A B :=
  distance_congr (.eqRefl _) (.eqRefl _) (one_mul A) (.eqRefl _)
    (distance_mul_left_one hB ht hd)

theorem power_near_one (q A B r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUnit : Γ ⊢[PRAAx] qnormSq q ≐ fraction one one)
    (hNear : Γ ⊢[PRAAx] distanceBounded q qone A B) : Γ ⊢[PRAAx]
    distanceBounded (power q r) qone (r*A) B :=
  distance_congr (.eqRefl _) (qone_power r) (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.unit_disk_power_difference q qone A B r hB
      (unit_bounded q hUnit) (unit_bounded qone norm_one) hNear)

/-- Generic exact rounded-power comparison, including zero exponents and
zero remainder. The numerical division identity is the sole arithmetic
premise; its producer can be any verified numerical quotient program. -/
theorem rounded_power_distance (q k a r P A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUnit : Γ ⊢[PRAAx] qnormSq q ≐ fraction one one)
    (hNear : Γ ⊢[PRAAx] distanceBounded q qone A B)
    (hP : Γ ⊢[PRAAx] P ≐ k*a+r) : Γ ⊢[PRAAx]
    distanceBounded (power (power q a) k) (power q P) (r*A) B := by
  have composed : Γ ⊢[PRAAx] power (power q a) k ≐ power q (k*a) :=
    (power_composition q a k).eqTrans (congrAp2 powerF (mul_comm a k) (.eqRefl q))
  have full : Γ ⊢[PRAAx] power q P ≐ qmul (power q (k*a)) (power q r) :=
    (congrAp2 powerF hP (.eqRefl q)).eqTrans (power_add q (k*a) r)
  have prefixUnit := unit_bounded _ (unit_power q (k*a) hUnit)
  have remainderBound := distance_symmetric _ _ _ _ hB (power_near_one q A B r hB hUnit hNear)
  have productBound := multiply_distance_bound (power q (k*a)) qone (power q r) (r*A) B hB prefixUnit remainderBound
  exact distance_congr ((GaussianReciprocalHorner.qmul_one_right _ (power_canonical q (k*a))).eqTrans composed.eqSymm)
    full.eqSymm (.eqRefl _) (.eqRefl _) productBound

def output (q k a r P A B : PTm n) : PTm n := pairT (power q a)
  (pairT (power (power q a) k) (pairT (power q P) (pairT (r*A) B)))
def outputF : PR 7 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
def run (q k a r P A B : PTm n) : PTm n := PTm.app outputF ![q,k,a,r,P,A,B]

ipra_subst output
ipra_subst run

theorem program_at (q k a r P A B : PTm n) : Γ ⊢[PRAAx] run q k a r P A B ≐ output q k a r P A B := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7) ![q,k,a,r,P,A,B]
theorem output_base (q k a r P A B : PTm n) : Γ ⊢[PRAAx] fstT (run q k a r P A B) ≐ power q a :=
  (program_at q k a r P A B).fstE
theorem output_rounded (q k a r P A B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run q k a r P A B)) ≐ power (power q a) k :=
  (program_at q k a r P A B).sndE.fstE
theorem output_full (q k a r P A B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run q k a r P A B))) ≐ power q P :=
  (program_at q k a r P A B).sndE.sndE.fstE
theorem output_numerator (q k a r P A B : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (sndT (run q k a r P A B)))) ≐ r*A :=
  (program_at q k a r P A B).sndE.sndE.sndE.fstE
theorem output_denominator (q k a r P A B : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (sndT (run q k a r P A B)))) ≐ B :=
  (program_at q k a r P A B).sndE.sndE.sndE.sndE

theorem program_certificate (q k a r P A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUnit : Γ ⊢[PRAAx] qnormSq q ≐ fraction one one)
    (hNear : Γ ⊢[PRAAx] distanceBounded q qone A B)
    (hP : Γ ⊢[PRAAx] P ≐ k*a+r) : Γ ⊢[PRAAx]
    le one (sndT (sndT (sndT (sndT (run q k a r P A B))))) ⋏
      distanceBounded (fstT (sndT (run q k a r P A B))) (fstT (sndT (sndT (run q k a r P A B))))
        (fstT (sndT (sndT (sndT (run q k a r P A B))))) (sndT (sndT (sndT (sndT (run q k a r P A B))))) :=
  .andI (le_congr (.eqRefl _) (output_denominator q k a r P A B).eqSymm hB)
    (distance_congr (output_rounded q k a r P A B).eqSymm (output_full q k a r P A B).eqSymm
      (output_numerator q k a r P A B).eqSymm (output_denominator q k a r P A B).eqSymm
      (rounded_power_distance q k a r P A B hB hUnit hNear hP))

theorem rational_qone_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (power qone (var 0) ≐ qone) := closeUniv 1 (qone_power _)
theorem rational_multiplication_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (qsub (qmul (var 0) (var 1)) (qmul (var 0) (var 2)) ≐ qmul (var 0) (qsub (var 1) (var 2))) :=
  closeUniv 3 (multiplication_difference _ _ _)
theorem rational_multiply_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 4) ⟶ bounded (var 0) one one ⟶ distanceBounded (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (qmul (var 0) (var 1)) (qmul (var 0) (var 2)) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (.impI (multiply_distance_bound _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem rational_power_near_one_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ qnormSq (var 0) ≐ fraction one one ⟶ distanceBounded (var 0) qone (var 1) (var 2) ⟶
      distanceBounded (power (var 0) (var 3)) qone (var 3*var 1) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (power_near_one _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem rational_rounded_power_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 6) ⟶ qnormSq (var 0) ≐ fraction one one ⟶ distanceBounded (var 0) qone (var 5) (var 6) ⟶
      var 4 ≐ var 1*var 2+var 3 ⟶
        distanceBounded (power (power (var 0) (var 2)) (var 1)) (power (var 0) (var 4)) (var 3*var 5) (var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (rounded_power_distance _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem rational_rounded_power_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ≐
      output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)) := closeUniv 7 (program_at _ _ _ _ _ _ _)
theorem rational_rounded_power_certificate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 6) ⟶ qnormSq (var 0) ≐ fraction one one ⟶ distanceBounded (var 0) qone (var 5) (var 6) ⟶
      var 4 ≐ var 1*var 2+var 3 ⟶
        (le one (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))) ⋏
          distanceBounded (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))
            (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))
            (fstT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))))))
            (sndT (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))))))) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (program_certificate _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianRationalRoundedPower
