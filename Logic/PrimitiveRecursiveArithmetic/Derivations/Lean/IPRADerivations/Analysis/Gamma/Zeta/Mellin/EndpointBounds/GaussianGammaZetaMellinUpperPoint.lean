import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinIntegrand
import IPRADerivations.Analysis.Euler.PositiveAxis.UpperBounds.GaussianEulerUpperPowerBound

/-!
# Inverse-square decay at the original Mellin observations

The denominator observation at a sufficiently late clock contains the
factorial monomial of order R+2 after its constant term has been removed.
Combine its reciprocal bound with the original power bound for t ≥ 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinUpperPoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEulerIntegrandName (powerF powerData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaZetaMellinIntegrand
  (exponentialF exponentialData denominatorF denominatorData denominatorClock denominator_at
    reciprocalF reciprocalData reciprocalClock reciprocal_at factorClock nameF data sample_at)
open GaussianPositiveExponentialProduct (positive_coefficient scalar_le_add)
open GaussianPositiveExponentialTermBound (actual_positive_fraction positive_suffix term_fraction)
open GaussianPositiveRealArithmetic (positive positive_add positive_congr)
open GaussianRationalExponentialTail (scalarPrefix tail prefix_split prefix_succ)
open GaussianRationalFiniteSum (sum_index_congr)
open GaussianRationalHorner (qadd canonical ofGaussian_canonical qadd_canonical positive_product)
open GaussianRationalLowerBounds (lower lower_congr inverse_bound)
open GaussianRationalMetric (bounded qsub qsub_canonical)
open GaussianRationalPolynomialExponential (scalarSum scalarBody scalar_sum_zero factorial_positive)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qone qsub_congr qadd_congr qadd_sub_cancel)
open GaussianScalarExponentialDiagonal (coefficient)
open Products (fact)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def degree (R : PTm n) : PTm n := R+two
def coefficientBound (R : PTm n) : PTm n := two*fact (degree R)

@[simp] theorem subst_degree {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (degree R) = degree (Syn.subst σ R) := by simp [degree,two]

@[simp] theorem subst_coefficientBound {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (coefficientBound R) = coefficientBound (Syn.subst σ R) := by simp [coefficientBound,two]

private theorem gap_parts (q j K : PTm n)
    (hj : Γ ⊢[PRAAx] le one j) (hK : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] qsub (scalarSum q K) qone ≐
      qadd (qadd (tail q one (monus j one)) (coefficient q j)) (tail q (succ j) (monus K j)) := by
  let P := tail q one (monus j one)
  let t := coefficient q j
  let Q := tail q (succ j) (monus K j)
  have start : Γ ⊢[PRAAx] scalarPrefix q j ≐ qadd qone P :=
    (sum_index_congr scalarBody (eq_add_of_le hj) (.eqRefl q)).eqTrans
      ((prefix_split q one (monus j one)).eqTrans (qadd_congr (scalar_sum_zero q) (.eqRefl P)))
  have length : Γ ⊢[PRAAx] succ K ≐ succ j+monus K j :=
    (congrSucc (eq_add_of_le hK)).eqTrans (succ_add j (monus K j)).eqSymm
  have block : Γ ⊢[PRAAx] scalarSum q K ≐ qadd (scalarPrefix q (succ j)) Q :=
    (sum_index_congr scalarBody length (.eqRefl q)).eqTrans (prefix_split q (succ j) (monus K j))
  have e : Γ ⊢[PRAAx] scalarSum q K ≐ qadd qone (qadd (qadd P t) Q) :=
    block.eqTrans ((qadd_congr ((prefix_succ q j).eqTrans
      ((qadd_congr start (.eqRefl t)).eqTrans (qadd_associative qone P t))) (.eqRefl Q)).eqTrans
        (qadd_associative qone (qadd P t) Q))
  exact (qsub_congr e (.eqRefl qone)).eqTrans (qadd_sub_cancel qone _ (qadd_canonical _ _))

theorem finite_gap_monomial (a b j K : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le one j) (hK : Γ ⊢[PRAAx] le j K) :
    Γ ⊢[PRAAx] lower (qsub (scalarSum (radiusPoint a b) K) qone)
      (pw a j) (fact j*pw b j) := by
  let q := radiusPoint a b
  let P := tail q one (monus j one)
  let t := coefficient q j
  let Q := tail q (succ j) (monus K j)
  let d := qsub (scalarSum q K) qone
  have hq := actual_positive_fraction a b hb
  have hp := positive_suffix q one (monus j one) hq
  have ht := positive_coefficient q j hq
  have hQ := positive_suffix q (succ j) (monus K j) hq
  have e := gap_parts q j K hj hK
  have ct := GaussianRationalHorner.qmul_canonical (Γ := Γ)
    (GaussianRationalPolynomialExponential.inverseFactorial j) (GaussianRationalReciprocal.power q j)
  have first : Γ ⊢[PRAAx] rationalLE (fstT t) (fstT (qadd P t)) :=
    rationalLE_congr (.eqRefl _) ((congrFst (GaussianRationalLinearProduct.qadd_commutative P t)).eqTrans
      (RationalGaussianRealPart.real_add t P)).eqSymm
      (scalar_le_add (fstT t) (fstT P) ct.andE₂.andE₁ hp.andE₂)
  have last : Γ ⊢[PRAAx] rationalLE (fstT (qadd P t)) (fstT (qadd (qadd P t) Q)) :=
    rationalLE_congr (.eqRefl _) (RationalGaussianRealPart.real_add (qadd P t) Q).eqSymm
      (scalar_le_add _ _ (qadd_canonical (Γ := Γ) P t).andE₂.andE₁ hQ.andE₂)
  exact GaussianExponentialAffineLower.lower_of_real_order d (pw a j) (fact j*pw b j)
    (positive_congr e.eqSymm (positive_add _ _ (positive_add _ _ hp ht) hQ)) (qsub_canonical _ _)
    (positive_product _ _ (factorial_positive j) (GaussianPolynomialPerturbation.power_positive b j hb))
    (rationalLE_congr (congrFst (term_fraction a b j hb)) (congrFst e).eqSymm (transitive first last))

private theorem index_covers_clock (R t : PTm n) :
    Γ ⊢[PRAAx] le t (GaussianRadiusExponentialName.index R t) := by
  let i := GaussianRadiusExponentialName.index R (zero : PTm n)
  have e : Γ ⊢[PRAAx] GaussianRadiusExponentialName.index R t ≐ i+t :=
    (GaussianRadiusExponentialName.index_congr R (zero_add t).eqSymm).eqTrans
      (GaussianRadiusExponentialName.index_add R zero t)
  exact le_congr (.eqRefl _) e.eqSymm (le_add_left t i)

theorem denominator_monomial (p a b j : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le one j) (hp : Γ ⊢[PRAAx] le j p) :
    Γ ⊢[PRAAx] lower (ap2 denominatorF p (denominatorData a b)) (pw a j) (fact j*pw b j) := by
  let x := radiusPoint a b
  let R := GaussianNameBounds.U constantF x
  let t := denominatorClock p
  let k := GaussianRadiusExponentialName.index R t
  let u := GaussianRadiusExponentialName.inputPrecision R t
  have hpt : Γ ⊢[PRAAx] le p t := le_add_right _ _
  have hk : Γ ⊢[PRAAx] le j k := le_trans (le_trans hp hpt) (index_covers_clock R t)
  have read : Γ ⊢[PRAAx] ap2 exponentialF t (exponentialData a b) ≐ scalarSum x k :=
    (GaussianRadiusExponentialName.sample_at (Γ := Γ) constantF R t x).eqTrans
      (sum_index_congr scalarBody (.eqRefl _) (constant_at u x))
  exact lower_congr ((denominator_at p a b).eqTrans (qsub_congr read (.eqRefl qone))).eqSymm
    (.eqRefl _) (.eqRefl _) (finite_gap_monomial a b j k hb hj hk)

theorem reciprocal_monomial (p a b j : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hj : Γ ⊢[PRAAx] le one j) (hp : Γ ⊢[PRAAx] le j p) :
    Γ ⊢[PRAAx] bounded (ap2 reciprocalF p (reciprocalData a b)) (fact j*pw b j) (pw a j) := by
  let r := reciprocalClock p b
  have later : Γ ⊢[PRAAx] le p r := le_trans (le_add_right _ _) (le_add_right _ _)
  have read := (reciprocal_at (Γ := Γ) p a b).eqTrans
    (GaussianNameReciprocal.reciprocal_congr (denominator_at r a b).eqSymm)
  exact bound_congr read.eqSymm (.eqRefl _) (.eqRefl _)
    (inverse_bound _ _ _ (GaussianPolynomialPerturbation.power_positive a j ha)
      (positive_product _ _ (factorial_positive j) (GaussianPolynomialPerturbation.power_positive b j hb))
      (denominator_monomial r a b j hb hj (le_trans hp later)))

private theorem square_power (a R : PTm n) : Γ ⊢[PRAAx] pw a (degree R) ≐ pw a R*(a*a) := by
  have sq : Γ ⊢[PRAAx] pw a two ≐ a*a :=
    (pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl a))
  exact (pw_add a R two).eqTrans (congrMul (.eqRefl _) sq)

theorem upper_observation_bound (p z R B a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerUpperPowerOrder.source z R B a b)
    (hp : Γ ⊢[PRAAx] le (degree R) p) :
    Γ ⊢[PRAAx] bounded (ap2 nameF p (data z B a b)) (coefficientBound R*(b*b)) (a*a) := by
  let k := factorClock p z B a b
  let u := ap2 powerF k (powerData z B a b)
  let v := ap2 reciprocalF k (reciprocalData a b)
  let j := degree R
  let U := unit k
  let A := pw a R
  let D := pw b R
  let f := fact j
  have ha := h.andE₂.andE₁.andE₁
  have hb := h.andE₂.andE₁.andE₂
  have hD := GaussianPolynomialPerturbation.power_positive (Γ := Γ) b R hb
  have hU := unit_positive (Γ := Γ) k
  have hbig : Γ ⊢[PRAAx] le j k := le_trans hp (le_add_right _ _)
  have hJ : Γ ⊢[PRAAx] le one j := le_trans (le_succ_self one) (le_add_left two R)
  have hpower : Γ ⊢[PRAAx] bounded u (two*A) D :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hD hU) hD
      (by
        change Γ ⊢[PRAAx] le ((A*U+D)*D) ((two*A)*(D*U))
        ipra_le 𝔞(D*U)*sl (pw_le_pw R h.andE₂.andE₂)+𝔞(D*D)*sl hU)
      (GaussianEulerUpperPowerBound.original_power_bound k z R B a b h)
  have hrecip : Γ ⊢[PRAAx] bounded v (f*pw b j) (pw a j) :=
    reciprocal_monomial k a b j ha hb hJ hbig
  have prod := bounded_product u v (two*A) D (f*pw b j) (pw a j) hD
    (GaussianPolynomialPerturbation.power_positive a j ha) hpower hrecip
  have numEq : Γ ⊢[PRAAx] (two*A)*(f*pw b j) ≐ (coefficientBound R*(b*b))*(A*D) :=
    (congrMul (.eqRefl _) (congrMul (.eqRefl _) (square_power b R))).eqTrans
      (by dsimp only [coefficientBound,f,j]; ipra_ring)
  have denEq : Γ ⊢[PRAAx] D*pw a j ≐ (a*a)*(A*D) :=
    (congrMul (.eqRefl _) (square_power a R)).eqTrans (by ipra_ring)
  have den := positive_product D (pw a j) hD (GaussianPolynomialPerturbation.power_positive a j ha)
  apply bounded_radius_mono _ _ _ _ _ den (positive_product _ _ ha ha) _
    (bound_congr (sample_at p z B a b).eqSymm (.eqRefl _) (.eqRefl _) prod)
  exact le_congr (congrMul numEq (.eqRefl _)).eqSymm (congrMul (.eqRefl _) denEq).eqSymm
    (le_of_eq_add (d := zero) (by ipra_ring))

theorem actual_mellin_upper_inverse_square_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((GaussianEulerUpperPowerOrder.source (var 1) (var 2) (var 3) (var 4) (var 5) ⋏
      le (degree (var 2)) (var 0)) ⟶
      bounded (ap2 nameF (var 0) (data (var 1) (var 3) (var 4) (var 5)))
        (coefficientBound (var 2)*(var 5*var 5)) (var 4*var 4)) :=
  closeUniv 6 (.impI (upper_observation_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinUpperPoint
