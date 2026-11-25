import IPRADerivations.Analysis.GaussianBinetBoseDenominator

/-!
# Cubic lower bound for every actual Bose denominator observation

The exact finite exponential sample retains its degree-three term
after subtraction of one. Positivity of the other terms and the
original rational Pi lower margin give a lower bound t³.
-/

set_option autoImplicit false
set_option maxHeartbeats 720000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseCubicGap

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseExponential (expRadius scaleF scaleData piClock scale_readback)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianPositiveExponentialProduct (scalar_le_add)
open GaussianPositiveExponentialTermBound (positive_suffix term_fraction actual_positive_fraction)
open GaussianPositiveRealArithmetic (positive positive_add positive_congr)
open GaussianRationalExponentialTail (scalarPrefix tail tail_succ prefix_split)
open GaussianRationalFiniteSum (sum_index_congr)
open GaussianRationalHorner (canonical qadd positive_product qadd_canonical)
open GaussianRationalLowerBounds (lower lower_congr)
open GaussianRationalMetric (qsub qsub_canonical)
open GaussianRationalPolynomialExponential (inverseFactorial factorial_positive scalarSum scalarBody)
open GaussianScalarExponentialDiagonal (coefficient)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qone qadd_congr qmul_congr qsub_congr qadd_sub_cancel)
open GaussianReciprocalHorner (qadd_commutative)
open RationalArgmin (rationalLE rationalLE_congr transitive)
open GaussianStirlingConstant (piNumerator piDenominator)
open GaussianBinetKernelPi (denominator_positive sample_margins)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Analysis.Products (fact)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "denomF" => GaussianBinetBoseDenominator.nameF
local notation "denomData" => GaussianBinetBoseDenominator.data

def cube (a : PTm n) : PTm n := a*a*a

@[simp] theorem subst_cube {m : ℕ} (σ : Fin n → PTm m) (a : PTm n) :
    Syn.subst σ (cube a) = cube (Syn.subst σ a) := by simp [cube]

theorem cube_positive (a : PTm n) (h : Γ ⊢[PRAAx] le one a) : Γ ⊢[PRAAx] le one (cube a) :=
  positive_product _ _ (positive_product _ _ h h) h

private theorem cube_power (a : PTm n) : Γ ⊢[PRAAx] pw a (num 3) ≐ cube a :=
  (pw_succ a (num 2)).eqTrans (congrMul ((pw_succ a one).eqTrans (congrMul (pw_one a) (.eqRefl a))) (.eqRefl a))

private theorem third_factorial : Γ ⊢[PRAAx] fact (num 3 : PTm n) ≐ num 6 := by
  let f0 := fact_zero (Γ := Γ) zero
  have f1 : Γ ⊢[PRAAx] fact (one : PTm n) ≐ one :=
    (fact_succ zero zero).eqTrans ((congrMul f0 (.eqRefl _)).eqTrans (by ipra_ring))
  have f2 : Γ ⊢[PRAAx] fact (num 2 : PTm n) ≐ num 2 :=
    (fact_succ one zero).eqTrans ((congrMul f1 (.eqRefl _)).eqTrans (by ipra_ring))
  exact (fact_succ (num 2) zero).eqTrans ((congrMul f2 (.eqRefl _)).eqTrans (by ipra_ring))

private theorem gap_readback (q K : PTm n) (hc : Γ ⊢[PRAAx] canonical q)
    (hK : Γ ⊢[PRAAx] le (num 3) K) :
    Γ ⊢[PRAAx] qsub (scalarSum q K) qone ≐ qadd (coefficient q (num 3))
      (qadd (qadd q (tail q two one)) (tail q (num 4) (monus K (num 3)))) := by
  let s := monus K (num 3)
  let v := tail q two one
  let w := tail q (num 4) s
  let t := coefficient q (num 3)
  have count : Γ ⊢[PRAAx] succ K ≐ num 4+s :=
    (congrSucc (eq_add_of_le hK)).eqTrans (by ipra_ring)
  have split : Γ ⊢[PRAAx] scalarSum q K ≐ qadd (scalarPrefix q (num 4)) w :=
    (sum_index_congr scalarBody count (.eqRefl q)).eqTrans (prefix_split q (num 4) s)
  have four : Γ ⊢[PRAAx] num 4 ≐ (two : PTm n)+succ one := by ipra_ring
  have three : Γ ⊢[PRAAx] two+one ≐ (num 3 : PTm n) := by ipra_ring
  have coeff : Γ ⊢[PRAAx] coefficient q (two+one) ≐ t := by
    unfold t coefficient
    apply qmul_congr
    · simpa only [GaussianRationalPolynomialExponential.subst_inverseFactorial,Syn.subst_var,Matrix.cons_val_zero] using
        Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (inverseFactorial (var 0) : PTm 1)
          (σ := ![two+one]) (σ' := ![num 3]) (fun j => by fin_cases j; exact three)
    · exact congrAp2 GaussianRationalReciprocal.powerF three (.eqRefl q)
  have small : Γ ⊢[PRAAx] tail q two (succ one) ≐ qadd v t :=
    (tail_succ q two one).eqTrans (qadd_congr (.eqRefl v) coeff)
  have short : Γ ⊢[PRAAx] scalarPrefix q (num 4) ≐ qadd (qadd qone q) (qadd v t) :=
    (sum_index_congr scalarBody four (.eqRefl q)).eqTrans
      ((prefix_split q two (succ one)).eqTrans (qadd_congr (GaussianExponentialAffineLower.affine_prefix q hc) small))
  have before : Γ ⊢[PRAAx] qadd (qadd qone q) (qadd v t) ≐ qadd qone (qadd t (qadd q v)) :=
    (qadd_associative qone q (qadd v t)).eqTrans
      (qadd_congr (.eqRefl _) ((qadd_associative q v t).eqSymm.eqTrans (qadd_commutative (qadd q v) t)))
  have joined := split.eqTrans ((qadd_congr (short.eqTrans before) (.eqRefl w)).eqTrans
    ((qadd_associative qone (qadd t (qadd q v)) w).eqTrans
      (qadd_congr (.eqRefl qone) (qadd_associative t (qadd q v) w))))
  exact (qsub_congr joined (.eqRefl _)).eqTrans
    (qadd_sub_cancel qone (qadd t (qadd (qadd q v) w)) (qadd_canonical _ _))

private theorem sample_index_cubic (R p : PTm n) :
    Γ ⊢[PRAAx] le (num 3) (GaussianRadiusExponentialName.index R p) := by
  have h : Γ ⊢[PRAAx] le (num 4) (GaussianRationalExponentialTail.cutoff R (p+num 4)) := by
    unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞(p)+2*𝔞(R)+2*𝔞(R)^2+4
  exact (succ_monus_succ (num 3) _).eqSymm.eqTrans
    (le_congr (.eqRefl _) (GaussianRationalExponentialTail.last_successor R (p+num 4)).eqSymm h)

private theorem finite_cubic_lower (a b A B K : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le (num 3) K)
    (hr : Γ ⊢[PRAAx] le (two*(A*b)) (a*B)) :
    Γ ⊢[PRAAx] lower (qsub (scalarSum (radiusPoint a b) K) qone) (cube A) (cube B) := by
  let q := radiusPoint a b
  let t := coefficient q (num 3)
  let v := qadd q (tail q two one)
  let w := tail q (num 4) (monus K (num 3))
  let g := qsub (scalarSum q K) qone
  let j : PTm n := num 3
  let c := fact j*pw b j
  have hq := actual_positive_fraction a b hb
  have hc : Γ ⊢[PRAAx] canonical q := GaussianRationalHorner.ofGaussian_canonical _ _ hb
  have rd := term_fraction a b j hb
  have rpos : Γ ⊢[PRAAx] le one c := positive_product _ _ (factorial_positive j)
    (GaussianPolynomialPerturbation.power_positive b j hb)
  have tc : Γ ⊢[PRAAx] canonical t := GaussianRationalHorner.canonical_congr rd
    (GaussianRationalHorner.ofGaussian_canonical _ _ rpos)
  have vp : Γ ⊢[PRAAx] positive v := positive_add _ _ hq (positive_suffix q two one hq)
  have wp : Γ ⊢[PRAAx] positive w := positive_suffix q (num 4) (monus K (num 3)) hq
  have tp : Γ ⊢[PRAAx] positive t := positive_congr rd.eqSymm (actual_positive_fraction _ _ rpos)
  have e := gap_readback q K hc hK
  have gp : Γ ⊢[PRAAx] positive g := positive_congr e.eqSymm (positive_add t (qadd v w) tp (positive_add v w vp wp))
  have vb := (positive_add v w vp wp).andE₂
  have mono : Γ ⊢[PRAAx] rationalLE (fstT t) (fstT g) :=
    rationalLE_congr (.eqRefl _) ((congrFst e).eqTrans (RationalGaussianRealPart.real_add t (qadd v w))).eqSymm
      (scalar_le_add _ _ tc.andE₂.andE₁ vb)
  have step : Γ ⊢[PRAAx] le (cube (two*(A*b))) (cube (a*B)) :=
    le_mul_mono (sq_le_sq hr) hr
  have lhs : Γ ⊢[PRAAx] le (c*cube A) (cube (two*(A*b))) := by
    have c6 : Γ ⊢[PRAAx] c ≐ num 6*cube b := congrMul third_factorial (cube_power b)
    exact le_congr (congrMul c6 (.eqRefl _)).eqSymm (.eqRefl _)
      (le_of_eq_add (d := two*cube (A*b)) (by unfold cube; ipra_ring))
  have clr : Γ ⊢[PRAAx] le (c*cube A) (pw a j*cube B) :=
    le_trans lhs (le_congr (.eqRefl _) ((congrMul (cube_power a) (.eqRefl _)).eqTrans
      (by unfold cube; ipra_ring)).eqSymm step)
  have hBB := cube_positive B hB
  have frac : Γ ⊢[PRAAx] rationalLE (fstT (radiusPoint (cube A) (cube B))) (fstT (radiusPoint (pw a j) c)) :=
    GaussianRationalMetric.comparison_of_cleared _ _ _ _ _ _ hBB rpos
      (GaussianPositiveExponentialOrder.radius_real_representation _ _ hBB)
      (GaussianPositiveExponentialOrder.radius_real_representation _ _ rpos) clr
  exact GaussianExponentialAffineLower.lower_of_real_order g (cube A) (cube B) gp (qsub_canonical _ _) hBB
    (transitive (rationalLE_congr (.eqRefl _) (congrFst rd).eqSymm frac) mono)

theorem denominator_lower (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] lower (ap2 denomF p (denomData A B)) (cube A) (cube B) := by
  let r := GaussianBinetBoseDenominator.sampleClock p
  let R := expRadius A
  let t := GaussianRadiusExponentialName.inputPrecision R r
  let k := piClock t A
  let a := (two*A)*piNumerator k
  let b := B*piDenominator k
  let K := GaussianRadiusExponentialName.index R r
  have hj := denominator_positive (Γ := Γ) k
  have hb := positive_product _ _ hB hj
  have pi := (sample_margins (Γ := Γ) k).andE₁
  have mono := le_trans (le_of_eq_add (d := piDenominator k) (by ipra_ring) :
    Γ ⊢[PRAAx] le (piDenominator k) (two*piDenominator k)) pi
  have order : Γ ⊢[PRAAx] le (two*(A*b)) (a*B) :=
    le_congr (by dsimp only [b]; ipra_ring) (by dsimp only [a]; ipra_ring)
      (mul_le_mul_right (two*A*B) mono)
  have get := (GaussianBinetBoseDenominator.sample_at (Γ := Γ) p A B).eqTrans
    (qsub_congr ((GaussianRadiusExponentialName.sample_at (Γ := Γ) scaleF R r (scaleData false A B)).eqTrans
      (sum_index_congr scalarBody (.eqRefl (succ K)) (scale_readback t A B hB))) (.eqRefl _))
  exact lower_congr get.eqSymm (.eqRefl _) (.eqRefl _)
    (finite_cubic_lower a b A B K hb hB (sample_index_cubic R r) order)

theorem actual_second_Binet_denominator_cubic_gap_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ lower (ap2 denomF (var 0) (denomData (var 1) (var 2))) (cube (var 1)) (cube (var 2))) :=
  closeUniv 3 (.impI (denominator_lower _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseCubicGap
