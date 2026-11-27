import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFixedEulerExponent
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedExponentBalance
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra

/-!
# Actual cancellation of the Euler constant in the folded Q exponent

The same cofinal Euler sample cancels only in an exact rational core.
Actual addition/multiplication samples retain their original clocks,
whose verified errors supply a computed diagonal envelope. This proves
that (E_(2R)-T_N)+z(gamma_N-gamma) equals the actual fixed Euler exponent
(gamma_N-H_(2R))z+T_(2R)-T_N at independent observation precisions.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFixedEulerExponentBalance

open_ipra
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianRationalHorner (qadd qmul ofGaussian)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint gammaF)
open GaussianGammaLogHarmonicName (fixedF fixed_regular)
open GaussianGammaFixedEulerExponent (differenceF differenceData difference_regular productF productData product_regular)
open GaussianGammaFoldedExponentBalance (correctionF correctionData correction_fast correctionCore correctionBudget correction_error pCore pBudget p_error)
open GaussianGammaFoldedMajorantExponent (input tail_source)
open GaussianNameRingLaws (three add_sample_error multiply_sample_error sum_left_error sum_right_error product_left_error through_identity equivalent_of_envelope)
open GaussianGeneralFTAConstants (ceilL1 ceil_norm_bound)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem finite_product_balance (g a l w : PTm n) : Γ ⊢[PRAAx]
    qadd (qmul (qsub g l) w) (qmul (qsub a g) w) ≐ qmul (qsub a l) w :=
  GaussianGammaFoldedExponentBalance.finite_product_balance g a l w

def fixedCore (p z B K N : PTm n) : PTm n :=
  qmul (qsub (ap2 fixedF p N) (harmonicPoint K)) (ofGaussian z B)
def fixedBudget (z B K N : PTm n) : PTm n :=
  (multiplyModulus differenceF constantF (differenceData K N) (ofGaussian z B)+one)
    +three*ceilL1 (ofGaussian z B)
def rawProductBudget (z B K N : PTm n) : PTm n := (pBudget z B K+correctionBudget z B N)+fixedBudget z B K N
ipra_subst fixedBudget [three]
ipra_subst rawProductBudget

theorem fixed_error (p z B K N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 productF p (productData z B K N)) (fixedCore p z B K N) (fixedBudget z B K N) (unit p) := by
  let w := ofGaussian z B
  let b := qsub (ap2 fixedF p N) (harmonicPoint K)
  have h := multiply_sample_error differenceF constantF (differenceData K N) w p (difference_regular K N hN) (constant_regular _)
  have d : Γ ⊢[PRAAx] distanceBounded (ap2 differenceF p (differenceData K N)) b three (unit p) :=
    distance_congr (.eqRefl _) (qadd_congr (.eqRefl _) (constant_at p _)) (.eqRefl _) (.eqRefl _)
      (add_sample_error fixedF constantF N (qnegative (harmonicPoint K)) p (fixed_regular N hN) (constant_regular _))
  exact distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (qmul_congr (.eqRefl _) (constant_at p w)) (.eqRefl _) (.eqRefl _) h)
    (product_left_error _ _ _ _ _ _ _ (unit_positive p) d (ceil_norm_bound w) (ceil_norm_bound b))

theorem raw_product_error (p z B K N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded
      (qadd (ap2 GaussianGammaCanonicalExponent.productF p (GaussianGammaCanonicalExponent.productData z B K))
        (ap2 correctionF p (correctionData z B N)))
      (ap2 productF p (productData z B K N)) (rawProductBudget z B K N) (unit p) := by
  have left := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (sum_left_error _ _ _ _ _ (unit_positive p) (p_error p z B K))
    (sum_right_error _ _ _ _ _ (unit_positive p) (correction_error p z B N hN))
  exact through_identity _ _ _ _ _ _ _ (unit_positive p) left (fixed_error p z B K N hN)
    (finite_product_balance (ap2 gammaF p zero) (ap2 fixedF p N) (harmonicPoint K) (ofGaussian z B))

/-- Two literal exchanges in the actual normalized rational sum. -/
theorem swap_last (a b c : PTm n) : Γ ⊢[PRAAx] qadd (qadd a b) c ≐ qadd (qadd a c) b :=
  (GaussianRationalSumAlgebra.qadd_associative a b c).eqTrans
    ((qadd_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_commutative b c)).eqTrans
      (GaussianRationalSumAlgebra.qadd_associative a c b).eqSymm)
theorem move_correction (a b c d : PTm n) : Γ ⊢[PRAAx]
    qadd (qadd (qadd a b) c) d ≐ qadd (qadd (qadd a d) b) c :=
  (swap_last (qadd a b) c d).eqTrans (qadd_congr (swap_last a b d) (.eqRefl _))

/-- The actual two tail attachments are compared at a common query;
no equality of retimed tail observations is assumed. -/
theorem attached_tail_error (f : PR 2) (x y z p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN GaussianGammaCanonicalTailName.pointF y)
    (hz : Γ ⊢[PRAAx] pointCN GaussianGammaCanonicalTailName.pointF z) : Γ ⊢[PRAAx]
    distanceBounded
      (ap2 (addF (addF f GaussianGammaCanonicalTailName.pointF) (GaussianNameRingLaws.negativeF GaussianGammaCanonicalTailName.pointF)) p
        (addData (addData x y) (GaussianNameRingLaws.negativeData z)))
      (qadd (qadd (ap2 f p x) (ap2 GaussianGammaCanonicalTailName.pointF p y))
        (ap2 (GaussianNameRingLaws.negativeF GaussianGammaCanonicalTailName.pointF) p (GaussianNameRingLaws.negativeData z)))
      (three+three) (unit p) :=
  distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (add_sample_error _ _ _ _ p (GaussianNameArithmetic.add_fast _ _ _ _ hf hy) (GaussianNameRingLaws.negative_fast _ _ hz))
    (sum_left_error _ _ _ _ _ (unit_positive p) (add_sample_error f GaussianGammaCanonicalTailName.pointF x y p hf hy))

def sumF : PR 2 := addF GaussianGammaFoldedMajorantExponent.combinedF correctionF
def sumData (z R B N : PTm n) : PTm n := addData (GaussianGammaFoldedMajorantExponent.combinedData z R B N) (correctionData z B N)
def balanceBudget (z R B N : PTm n) : PTm n :=
  ((three+(three+three))+rawProductBudget z B (two*R) N)+(three+three)
ipra_subst sumData
ipra_subst balanceBudget [three]

theorem balance_at (p z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 sumF p (sumData z R B N))
      (ap2 GaussianGammaFixedEulerExponent.combinedF p (GaussianGammaFixedEulerExponent.combinedData z R B N))
      (balanceBudget z R B N) (unit p) := by
  let Y := GaussianGammaCanonicalTailName.data z R B (two*R)
  let Z := GaussianGammaCanonicalTailName.data z R B N
  have hn := (tail_source z R B N h).andE₂.andE₁
  have hy := GaussianGammaCanonicalTailName.name_regular z R B (two*R) (GaussianGammaCanonicalExponent.tail_source z R B h.andE₁)
  have hz := GaussianGammaCanonicalTailName.name_regular z R B N (tail_source z R B N h)
  have left := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (add_sample_error GaussianGammaFoldedMajorantExponent.combinedF correctionF _ _ p
      (GaussianGammaFoldedMajorantExponent.combined_regular z R B N h) (correction_fast z B N hn))
    (sum_left_error _ _ _ _ _ (unit_positive p)
      (attached_tail_error GaussianGammaCanonicalExponent.productF (GaussianGammaCanonicalExponent.productData z B (two*R)) Y Z p
        (GaussianGammaCanonicalExponent.product_regular z B (two*R)) hy hz))
  have raw := sum_left_error _ _
    (ap2 (GaussianNameRingLaws.negativeF GaussianGammaCanonicalTailName.pointF) p (GaussianNameRingLaws.negativeData Z)) _ _ (unit_positive p)
    (sum_left_error _ _ (ap2 GaussianGammaCanonicalTailName.pointF p Y) _ _ (unit_positive p)
      (raw_product_error p z B (two*R) N hn))
  have chain := distance_triangle_same _ _ _ _ _ _ (unit_positive p)
    (distance_congr (.eqRefl _) (move_correction _ _ _ _) (.eqRefl _) (.eqRefl _) left) raw
  exact through_identity _ _ _ _ _ _ _ (unit_positive p) chain
    (attached_tail_error productF (productData z B (two*R) N) Y Z p (product_regular z B (two*R) N hn) hy hz) (.eqRefl _)

theorem balanced_exponents (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    crossEquivalent sumF GaussianGammaFixedEulerExponent.combinedF (sumData z R B N)
      (GaussianGammaFixedEulerExponent.combinedData z R B N) := by
  have hn := (tail_source z R B N h).andE₂.andE₁
  apply equivalent_of_envelope _ _ _ _ (balanceBudget z R B N)
    (GaussianNameArithmetic.add_fast _ _ _ _ (GaussianGammaFoldedMajorantExponent.combined_regular z R B N h) (correction_fast z B N hn))
    (GaussianGammaFixedEulerExponent.combined_regular z R B N h)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  change Γ.map Fm.shift ⊢[PRAAx] distanceBounded
    (ap2 sumF (var 0) (Syn.shift (sumData z R B N)))
    (ap2 GaussianGammaFixedEulerExponent.combinedF (var 0) (Syn.shift (GaussianGammaFixedEulerExponent.combinedData z R B N)))
    (Syn.shift (balanceBudget z R B N)) (unit (var 0))
  rw [show Syn.shift (sumData z R B N) = sumData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) from subst_sumData _ _ _ _ _,
    show Syn.shift (GaussianGammaFixedEulerExponent.combinedData z R B N) =
      GaussianGammaFixedEulerExponent.combinedData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) from
      GaussianGammaFixedEulerExponent.subst_combinedData _ _ _ _ _,
    show Syn.shift (balanceBudget z R B N) = balanceBudget (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) from
      subst_balanceBudget _ _ _ _ _]
  exact balance_at (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift N) hs

theorem actual_fixed_euler_core_cancellation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (qadd (qmul (qsub (var 0) (var 2)) (var 3)) (qmul (qsub (var 1) (var 0)) (var 3)) ≐
      qmul (qsub (var 1) (var 2)) (var 3)) := closeUniv 4 (finite_product_balance _ _ _ _)
theorem original_fixed_euler_exponents_balance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent sumF GaussianGammaFixedEulerExponent.combinedF
      (sumData (var 0) (var 1) (var 2) (var 3)) (GaussianGammaFixedEulerExponent.combinedData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (balanced_exponents _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaFixedEulerExponentBalance
