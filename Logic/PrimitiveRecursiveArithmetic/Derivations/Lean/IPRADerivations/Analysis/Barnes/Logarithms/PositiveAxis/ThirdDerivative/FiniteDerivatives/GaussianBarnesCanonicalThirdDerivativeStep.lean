import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.FiniteDerivatives.GaussianBarnesCanonicalThirdDerivativeAlgebra
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.HigherOrders.GaussianBarnesCanonicalHigherRows
import IPRADerivations.Analysis.LinearAlgebra.Determinants.GaussianScalarColumnSelection

/-!
# The original second logarithmic row differentiates to the original cubic row

Fractional lower bounds on the unshifted and shifted bases provide an
inverse bound K. The exact remainder has two displacement factors,
four inverse factors, and three powers of the row index in the denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativeStep

open_ipra
open LeanProofs.IPRA.Common (pw_two)
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalDerivativeRow (offset)
open GaussianBarnesCanonicalDeflatedFactor (inverseInteger)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalHigherRows (derivative)
open GaussianBarnesCanonicalSecondDerivativeStep (base_difference step_factor step_bound)
open GaussianBarnesCanonicalThirdDerivativeAlgebra (doubleSquare inverseWeight residual)
open GaussianDominantPairAlgebra (radiusPoint radius_multiply radius_congr radius_one)
open GaussianNameArithmetic (sum_difference)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalHorner (ofGaussian positive_product qadd qmul qmul_canonical qzero)
open GaussianRationalLowerBounds (lower)
open GaussianRationalMetric (bounded distanceBounded qnegative qsub qsub_canonical)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (bounded_sum_same)
open GaussianRationalReciprocal
  (bounded_negative bounded_product bound_congr power power_succ qone reciprocal)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr qzero_add)
open GaussianReciprocalHorner (qadd_commutative qmul_associative qmul_one_right)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "second" => GaussianBarnesCanonicalSecondDerivativeRow.value

def source (z h B k H K : PTm n) : Fm PTm n :=
  le one B ⋏ (le one k ⋏ (le one K ⋏
    (lower (base z B k) one K ⋏
      (lower (base (add z h) B k) one K ⋏ ComplexLogarithmRemainder.bounded h H))))

def increment (z h B k : PTm n) : PTm n := qsub (second (add z h) B k) (second z B k)

def linear (z h B k : PTm n) : PTm n := qmul (ofGaussian h B) (derivative z B k zero)

def remainder (z h B k : PTm n) : PTm n :=
  let i := reciprocal (base z B k)
  let j := reciprocal (base (add z h) B k)
  let u := qmul (offset h B k) i
  qmul (inverseInteger k) (qmul u (qmul (qnegative (qmul u j)) (inverseWeight i j)))

def errorNumerator (H K : PTm n) : PTm n := num 3*H*H*(K*K*K*K)

def errorDenominator (B k : PTm n) : PTm n := (B*B)*(k*k*k)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h B k H K : PTm n) :
    (source z h B k H K).subst σ =
      source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) (Syn.subst σ K) :=
  by simp [source,one]

@[simp] theorem subst_increment {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (increment z h B k) = increment (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [increment]

@[simp] theorem subst_linear {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (linear z h B k) = linear (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [linear]

@[simp] theorem subst_errorNumerator {m : ℕ} (σ : Fin n → PTm m) (H K : PTm n) :
    Syn.subst σ (errorNumerator H K) = errorNumerator (Syn.subst σ H) (Syn.subst σ K) :=
  by simp [errorNumerator]

@[simp] theorem subst_errorDenominator {m : ℕ} (σ : Fin n → PTm m) (B k : PTm n) :
    Syn.subst σ (errorDenominator B k) = errorDenominator (Syn.subst σ B) (Syn.subst σ k) :=
  by simp [errorDenominator]

private theorem signed_cube (q : PTm n) :
    Γ ⊢[PRAAx] qnegative (power (qnegative q) (succ two)) ≐ qmul (qmul q q) q := by
  let t := qmul q q
  have sq : Γ ⊢[PRAAx] power (qnegative q) two ≐ t :=
    (GaussianRationalInverseQuadraticAlgebra.power_two_raw (qnegative q)).eqTrans
      (GaussianScalarColumnSelection.negative_both_product q q)
  have cube : Γ ⊢[PRAAx] power (qnegative q) (succ two) ≐ qnegative (qmul t q) :=
    (power_succ (qnegative q) two).eqTrans ((qmul_congr sq (.eqRefl _)).eqTrans
      ((qmul_commutative t (qnegative q)).eqTrans
        ((GaussianInverseBinomialRows.negative_product q t).eqSymm.eqTrans
          (GaussianInverseBinomialRows.negative_congr (qmul_commutative q t)))))
  exact (GaussianInverseBinomialRows.negative_congr cube).eqTrans
    (GaussianDeterminantSignTransport.negative_involution _ (qmul_canonical t q))

private theorem factor_two : Γ ⊢[PRAAx] fact (two : PTm n) ≐ two := by
  have first : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul (fact_zero zero) (.eqRefl one)).eqTrans (one_mul one))
  exact (fact_succ one zero).eqTrans ((congrMul first (.eqRefl two)).eqTrans (one_mul two))

private theorem two_point : Γ ⊢[PRAAx] qadd qone qone ≐ radiusPoint (two : PTm n) one := by
  let a := GaussianDominantPairAlgebra.radiusNumerator (one : PTm n)
  let b := GaussianDominantPairAlgebra.radiusNumerator (two : PTm n)
  have h : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (add a a) b := by
    apply GaussianRootAlgebra.equal_of_values
    · simp only [a,b,GaussianDominantPairAlgebra.radiusNumerator,GaussianRootAlgebra.re_add,
        ComplexLogarithmRemainder.eval_re_code,ZT.toZ_ofNat]
      ipra_simps
      ring
    · simp only [a,b,GaussianDominantPairAlgebra.radiusNumerator,GaussianRootAlgebra.im_add,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
      ipra_simps
      ring
  exact GaussianRationalHorner.canonical_unique _ _ b one (GaussianRationalHorner.qadd_canonical _ _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
    (GaussianRationalHorner.represents_congr (.eqRefl _) h (.eqRefl _)
      (GaussianRationalHorner.qadd_represents _ _ _ _ _ (le_refl one)
        (GaussianRationalHorner.represents_congr radius_one (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
          (GaussianDominantPairAlgebra.radius_represents _ _ (le_refl one)))
        (GaussianRationalHorner.represents_congr radius_one (GaussianRootAlgebra.equal_refl _) (.eqRefl _)
          (GaussianDominantPairAlgebra.radius_represents _ _ (le_refl one)))))
    (GaussianDominantPairAlgebra.radius_represents _ _ (le_refl one))

private theorem scalar_weight (k : PTm n) (hk : Γ ⊢[PRAAx] le one k) :
    Γ ⊢[PRAAx] radiusPoint (fact two) (pw k two) ≐
      qmul (inverseInteger k) (qmul (inverseInteger k) (qadd qone qone)) := by
  have inner : Γ ⊢[PRAAx] qmul (inverseInteger k) (qadd qone qone) ≐ radiusPoint two k :=
    (qmul_congr (.eqRefl _) two_point).eqTrans
      ((radius_multiply one k two one hk (le_refl one)).eqTrans
        (radius_congr (one_mul two) (by ipra_ring)))
  exact ((qmul_congr (.eqRefl (inverseInteger k)) inner).eqTrans
    ((radius_multiply one k two k hk hk).eqTrans
      (radius_congr ((one_mul two).eqTrans (factor_two (Γ := Γ)).eqSymm) (pw_two k).eqSymm))).eqSymm

private theorem middle_swap (x y z : PTm n) :
    Γ ⊢[PRAAx] qmul x (qmul y z) ≐ qmul y (qmul x z) :=
  GaussianRationalPowerAlgebra.commute_nested x y z

theorem linear_expansion (z h B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hk : Γ ⊢[PRAAx] le one k) :
    let i := reciprocal (base z B k)
    Γ ⊢[PRAAx] linear z h B k ≐
      qmul (inverseInteger k) (qmul (qmul (offset h B k) i) (doubleSquare i)) := by
  let i := reciprocal (base z B k)
  let d := ofGaussian h B
  let s := inverseInteger k
  let v := qmul i i
  let c := qmul v i
  let w : PTm n := qadd qone qone
  have read : Γ ⊢[PRAAx] linear z h B k ≐ qmul d (qmul c (qmul s (qmul s w))) :=
    qmul_congr (.eqRefl _) (qmul_congr (signed_cube i) (scalar_weight k hk))
  have move : Γ ⊢[PRAAx] qmul d (qmul c (qmul s (qmul s w))) ≐ qmul s (qmul (qmul d s) (qmul c w)) :=
    (qmul_congr (.eqRefl _) (middle_swap c s (qmul s w))).eqTrans
      ((middle_swap d s (qmul c (qmul s w))).eqTrans
        (qmul_congr (.eqRefl _) ((qmul_congr (.eqRefl _) (middle_swap c s w)).eqTrans
          (qmul_associative d s (qmul c w)).eqSymm)))
  have doubled : Γ ⊢[PRAAx] qmul c w ≐ qmul i (doubleSquare i) := by
    have wc : Γ ⊢[PRAAx] qmul c w ≐ qadd c c :=
      (qmul_add c qone qone).eqTrans
        (qadd_congr (qmul_one_right c (qmul_canonical v i)) (qmul_one_right c (qmul_canonical v i)))
    exact wc.eqTrans ((qadd_congr (qmul_commutative v i) (qmul_commutative v i)).eqTrans (qmul_add i v v).eqSymm)
  exact read.eqTrans (move.eqTrans
    (qmul_congr (.eqRefl _) ((qmul_congr (step_factor h B k hB hk) doubled).eqTrans
      (qmul_associative (offset h B k) i (doubleSquare i)).eqSymm)))

private theorem inverse_difference (z h B k H K : PTm n) (hs : Γ ⊢[PRAAx] source z h B k H K) :
    let i := reciprocal (base z B k)
    let j := reciprocal (base (add z h) B k)
    Γ ⊢[PRAAx] qsub i j ≐ qmul (qmul (offset h B k) i) j := by
  let b := base z B k
  let c := base (add z h) B k
  let i := reciprocal b
  let d := offset h B k
  have hK := hs.andE₂.andE₂.andE₁
  have h₁ := GaussianNameReciprocal.lower_norm_positive b K hK hs.andE₂.andE₂.andE₂.andE₁
  have h₂ := GaussianNameReciprocal.lower_norm_positive c K hK hs.andE₂.andE₂.andE₂.andE₂.andE₁
  exact (GaussianNameReciprocal.inverse_difference b c h₁ h₂).eqTrans
    (qmul_congr ((qmul_congr (.eqRefl i) (base_difference z h B k hs.andE₁ hs.andE₂.andE₁)).eqTrans
      (qmul_commutative i d)) (.eqRefl _))

theorem exact_remainder (z h B k H K : PTm n) (hs : Γ ⊢[PRAAx] source z h B k H K) :
    Γ ⊢[PRAAx] qsub (increment z h B k) (linear z h B k) ≐ remainder z h B k := by
  let i := reciprocal (base z B k)
  let j := reciprocal (base (add z h) B k)
  let d := offset h B k
  let s := inverseInteger k
  let v := qmul i i
  let w := qmul j j
  have inner : Γ ⊢[PRAAx] qsub (qsub qone w) (qsub qone v) ≐ qsub v w := by
    have cancel : Γ ⊢[PRAAx] qsub (qnegative w) (qnegative v) ≐ qsub v w :=
      (qadd_congr (.eqRefl _) (GaussianDeterminantSignTransport.negative_involution _ (qmul_canonical i i))).eqTrans
        (qadd_commutative (qnegative w) v)
    exact (GaussianNameArithmetic.sum_difference_cancel_left qone (qnegative w) (qnegative v)).eqTrans cancel
  have inc : Γ ⊢[PRAAx] increment z h B k ≐ qmul s (qsub v w) :=
    (multiplication_difference s (qsub qone w) (qsub qone v)).eqTrans (qmul_congr (.eqRefl _) inner)
  have lin := linear_expansion z h B k hs.andE₁ hs.andE₂.andE₁
  have e := inverse_difference z h B k H K hs
  have neg := (GaussianRationalDistanceOrder.reversed_difference (Γ := Γ) i j).eqSymm.eqTrans
    (GaussianInverseBinomialRows.negative_congr e)
  exact (qsub_congr inc lin).eqTrans ((multiplication_difference s (qsub v w) (qmul (qmul d i) (doubleSquare i))).eqTrans
    (qmul_congr (.eqRefl _) ((residual i j d e).eqTrans
      (qmul_congr (.eqRefl _) (qmul_congr neg (.eqRefl _))))))

theorem quadratic_bound (z h B k H K : PTm n) (hs : Γ ⊢[PRAAx] source z h B k H K) :
    Γ ⊢[PRAAx] distanceBounded (increment z h B k) (linear z h B k) (errorNumerator H K) (errorDenominator B k) := by
  let i := reciprocal (base z B k)
  let j := reciprocal (base (add z h) B k)
  let d := offset h B k
  let u := qmul d i
  let v := qnegative (qmul u j)
  let w := inverseWeight i j
  let D := B*k
  let s := inverseInteger k
  have hB := hs.andE₁
  have hk := hs.andE₂.andE₁
  have hK := hs.andE₂.andE₂.andE₁
  have hD := positive_product _ _ hB hk
  have ho : Γ ⊢[PRAAx] le one (one : PTm n) := le_refl one
  have db : Γ ⊢[PRAAx] bounded d H D := step_bound h B k H hB hk hs.andE₂.andE₂.andE₂.andE₂.andE₂
  have ib : Γ ⊢[PRAAx] bounded i K one :=
    GaussianRationalLowerBounds.inverse_bound _ one K ho hK hs.andE₂.andE₂.andE₂.andE₁
  have jb : Γ ⊢[PRAAx] bounded j K one :=
    GaussianRationalLowerBounds.inverse_bound _ one K ho hK hs.andE₂.andE₂.andE₂.andE₂.andE₁
  have ub : Γ ⊢[PRAAx] bounded u (H*K) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product d i H D K one hD ho db ib)
  have vb : Γ ⊢[PRAAx] bounded v (H*K*K) D :=
    bounded_negative _ _ _ hD
      (bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product u j (H*K) D K one hD ho ub jb))
  have wb : Γ ⊢[PRAAx] bounded w (K+K+K) one :=
    bounded_sum_same _ _ _ _ _ ho (bounded_sum_same i i K K one ho ib ib) jb
  have vw : Γ ⊢[PRAAx] bounded (qmul v w) (H*K*K*(K+K+K)) D :=
    bound_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (bounded_product v w (H*K*K) D _ one hD ho vb wb)
  have prod := bounded_product u (qmul v w) _ D _ D hD hD ub vw
  have sInv := GaussianBarnesCanonicalSecondDerivativeRow.inverse_integer_bound k hk
  have all := bounded_product s (qmul u (qmul v w)) one k _ (D*D) hk (positive_product _ _ hD hD) sInv prod
  exact bound_congr (exact_remainder z h B k H K hs).eqSymm
    (by unfold errorNumerator; ipra_ring)
    (by dsimp only [D,errorDenominator]; ipra_ring) all

theorem actual_Barnes_second_logarithmic_row_third_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let B := var 2
     let k := var 3
     let H := var 4
     let K := var 5
     source z h B k H K ⟶
       (qsub (increment z h B k) (linear z h B k) ≐ remainder z h B k ⋏
         distanceBounded (increment z h B k) (linear z h B k) (errorNumerator H K) (errorDenominator B k))) :=
  closeUniv 6 (.impI (.andI (exact_remainder _ _ _ _ _ _ Prf.hyp0) (quadratic_bound _ _ _ _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalThirdDerivativeStep
