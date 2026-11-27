import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingUnitDifferenceAlgebra
import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalMean
import IPRADerivations.Analysis.Integration.CompactGrids.Splits.GaussianCompactRiemannSplit
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianEulerBetaPrimitivePascal
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Exact finite weighted resolvent on the Binet unit grid

At the original tag `u = j/M`, the actual product
`(1/2 - u) * reciprocal(z + u)` is `(z + 1/2)/(z + u) - 1`.
After the original uniform left sum, the mean of the constant one
is exactly one.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedResolventGrid

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianBinetReciprocalRows (tagPoint)
open GaussianBinetStirlingUnitDifferenceAlgebra (coefficient)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalFiniteSum (sum multiplyBody termsEqual)
open GaussianRationalHorner (qadd qmul ofGaussian_represents ofGaussian_canonical canonical_unique represents_congr positive_product)
open GaussianRationalMetric (qsub qnegative qsub_canonical qsub_represents qnegative_canonical)
open GaussianRationalNaturalScale (naturalPoint natScale natScale_as_product)
open GaussianRationalNormalizedTelescope (weight weight_sum_one)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalReciprocal (reciprocal reciprocal_identity)
open GaussianRationalSyntheticDivision (qone qsub_congr qadd_congr qmul_congr)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rows" => GaussianBinetReciprocalMean.rowBody
local notation "reciprocalData" => GaussianBinetReciprocalMean.data

def gridData (A B D sign M : PTm n) : PTm n := pairT M (reciprocalData A B D sign zero M)

def rowBody : PTm 2 := qmul (qsub (fraction one two) (fraction (var 0) (fstT (var 1))))
  (inst2 rows (var 0) (sndT (var 1)))

def value (A B D sign M : PTm n) : PTm n := qmul (weight M) (sum rowBody M (gridData A B D sign M))

ipra_subst gridData

ipra_subst value

private theorem base_congr {A A' B D sign : PTm n} (hA : Γ ⊢[PRAAx] A ≐ A') :
    Γ ⊢[PRAAx] argument A B D sign ≐ argument A' B D sign := by
  simpa only [subst_argument,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (argument (var 0) (var 1) (var 2) (var 3) : PTm 4) (σ := ![A,B,D,sign]) (σ' := ![A',B,D,sign])
      (fun i => by fin_cases i; exact hA; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _)

theorem tag_add (A B D sign M j : PTm n) (h : Γ ⊢[PRAAx] source A D sign) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] tagPoint A B D sign zero M j ≐ qadd (argument A B D sign) (fraction j M) := by
  let a := A+zero*D
  let X := M*a
  let Y := M*B
  let E := M*D
  let t := argument (X+j*D) Y E sign
  let b := argument X Y E sign
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hM h.andE₂
  have ha := GaussianLogGammaEulerHead.shifted_source zero A D sign h
  have eb : Γ ⊢[PRAAx] b ≐ argument A B D sign :=
    (GaussianLogGammaEulerChartAgreement.scaled_argument a B D sign M E ha hM (.eqRefl E)).eqTrans
      (base_congr (by dsimp only [a]; ipra_ring))
  have rep := qsub_represents t b (native (X+j*D) Y sign) (native X Y sign) E he
    (ofGaussian_represents _ _ he) (ofGaussian_represents _ _ he)
  have diff : Γ ⊢[PRAAx] qsub t b ≐ fraction (j*D) E :=
    canonical_unique _ _ _ _ (qsub_canonical _ _) (ofGaussian_canonical _ _ he) he
      (represents_congr (.eqRefl _) (GaussianBinetReciprocalRows.same_imaginary_shift X (j*D) Y sign)
        (.eqRefl _) rep) (ofGaussian_represents _ _ he)
  have unitTime : Γ ⊢[PRAAx] fraction (j*D) E ≐ fraction j M :=
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (mul_comm j D) (mul_comm M D)).eqTrans
      (GaussianCompactRiemannSplit.fraction_cancel D j M h.andE₂ hM)
  exact (GaussianRationalLinearProduct.add_sub_right b t (ofGaussian_canonical _ _ he)).eqSymm.eqTrans
    (qadd_congr eb (diff.eqTrans unitTime))

theorem row_at (A B D sign M j : PTm n) :
    Γ ⊢[PRAAx] inst2 rowBody j (gridData A B D sign M) ≐
      qmul (qsub (fraction one two) (fraction j M)) (reciprocal (tagPoint A B D sign zero M j)) := by
  let x := reciprocalData A B D sign zero M
  have expand (i d : PTm n) : inst2 rowBody i d =
      qmul (qsub (fraction one two) (fraction i (fstT d))) (inst2 rows i (sndT d)) := by
    change Syn.subst ![i,d] (qmul _ _) = _
    simp only [GaussianRationalHorner.subst_qmul,GaussianRationalMetric.subst_qsub,
      GaussianPositiveRationalLogarithm.subst_fraction,subst_fstT,subst_sndT,subst_inst2,
      one,two,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.subst_var,
      Matrix.cons_val_zero,Matrix.cons_val_one]
  have tag := (congrInst2 rows (.eqRefl j) (snd_pair (Γ := Γ) M x)).eqTrans
    (GaussianBinetReciprocalMean.tag_at A B D sign zero M j)
  rw [expand]
  exact qmul_congr (qsub_congr (.eqRefl (fraction one two))
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (.eqRefl j) (fst_pair M x))) tag

theorem tag_identity (A B D sign M j : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] inst2 rowBody j (gridData A B D sign M) ≐
      qsub (qmul (coefficient A B D sign) (reciprocal (tagPoint A B D sign zero M j))) qone := by
  let z := argument A B D sign
  let a := M*(A+zero*D)+j*D
  let E := M*D
  let t := tagPoint A B D sign zero M j
  let c := coefficient A B D sign
  let u := fraction j M
  let v : PTm n := fraction one two
  have ha : Γ ⊢[PRAAx] le one a := le_trans (positive_product _ _ hM
    (GaussianLogGammaEulerHead.shifted_source zero A D sign h).andE₁.andE₁) (le_add_right _ _)
  have he : Γ ⊢[PRAAx] le one E := positive_product _ _ hM h.andE₂
  have ht : Γ ⊢[PRAAx] source a E sign := .andI (.andI ha h.andE₁.andE₂) he
  have hn := GaussianNameReciprocal.lower_norm_positive t E he
    (GaussianRationalLowerBounds.name_lower t a E ha he (GaussianBinetReciprocalRows.real_part_lower a (M*B) E sign ht))
  have diff : Γ ⊢[PRAAx] qsub c t ≐ qsub v u :=
    (qsub_congr (.eqRefl c) (tag_add A B D sign M j h hM)).eqTrans
      ((GaussianNameArithmetic.sum_difference z z v u).eqTrans
        ((qadd_congr (GaussianCoefficientNormOrder.qsub_self z) (.eqRefl _)).eqTrans
          (GaussianRationalSyntheticDivision.qzero_add _ (qsub_canonical _ _))))
  exact (row_at A B D sign M j).eqTrans
    ((qmul_congr diff.eqSymm (.eqRefl _)).eqTrans
      ((GaussianEulerBetaPrimitivePascal.right_product_difference c t (reciprocal t)).eqTrans
        (qsub_congr (.eqRefl _) (reciprocal_identity t hn))))

private def affineBody : PTm 2 := GaussianRationalFiniteSum.addBody (multiplyBody rows) (qnegative qone)

private theorem affine_at (i c x : PTm n) :
    Γ ⊢[PRAAx] inst2 affineBody i (pairT c x) ≐ qsub (qmul c (inst2 rows i x)) qone := by
  rw [affineBody, GaussianRationalFiniteSum.inst2_addBody]
  have con : inst2 (qnegative (qone : PTm 2)) i (pairT c x) = qnegative (qone : PTm n) := by simp [inst2]
  rw [con]
  exact qadd_congr (GaussianRationalFiniteSum.multiply_body_at rows c i x) (.eqRefl _)

private theorem affine_sum (c x M : PTm n) :
    Γ ⊢[PRAAx] sum affineBody M (pairT c x) ≐ qadd (qmul c (sum rows M x)) (natScale M (qnegative qone)) := by
  have constantRead : Γ ⊢[PRAAx] sum (qnegative qone) M (pairT c x) ≐
      sum GaussianRationalRiemannRefinement.constantBody M (qnegative qone) := by
    apply GaussianRationalFiniteSum.sum_congr_bounded
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift M) :: Γ.map Fm.shift
    change Δ ⊢[PRAAx] inst2 (qnegative qone) (var 0) (Syn.shift (pairT c x)) ≐
      inst2 GaussianRationalRiemannRefinement.constantBody (var 0) (Syn.shift (qnegative qone))
    rw [GaussianRationalRiemannRefinement.constant_entry]
    simpa only [Syn.shift,inst2,GaussianRationalMetric.subst_qnegative,GaussianRationalSyntheticDivision.subst_qone] using
      (Prf.eqRefl (qnegative qone : PTm (n+1)) : Δ ⊢[PRAAx] _)
  exact (GaussianRationalFiniteSum.sum_add (multiplyBody rows) (qnegative (qone : PTm 2)) M (pairT c x)).eqTrans
    (qadd_congr (GaussianRationalFiniteSum.sum_multiply rows c M x)
      (constantRead.eqTrans (GaussianRationalRiemannRefinement.constant_sum (qnegative qone) M)))

theorem finite_identity (A B D sign M : PTm n) (h : Γ ⊢[PRAAx] source A D sign) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] value A B D sign M ≐
      qsub (qmul (coefficient A B D sign) (GaussianBinetReciprocalMean.value A B D sign zero M)) qone := by
  let c := coefficient A B D sign
  let x := reciprocalData A B D sign zero M
  let u := sum rows M x
  let w := weight M
  let v : PTm n := qnegative qone
  have rows_eq : Γ ⊢[PRAAx] termsEqual rowBody affineBody M (gridData A B D sign M) (pairT c x) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] source (s A) (s D) (s sign) := by
      simpa [Δ,s,Fm.shift,Syn.shift,source,GaussianRightHalfPlaneArgument.source] using h.shift.wk
    have hm : Δ ⊢[PRAAx] le one (s M) := (Order.shift_one_le hM).wk
    have right := (affine_at (Γ := Δ) (var 0) (coefficient (s A) (s B) (s D) (s sign))
      (reciprocalData (s A) (s B) (s D) (s sign) zero (s M))).eqTrans
        (qsub_congr (qmul_congr (.eqRefl _) (GaussianBinetReciprocalMean.tag_at (s A) (s B) (s D) (s sign) zero (s M) (var 0)))
          (.eqRefl _))
    simpa only [Syn.shift,s,Δ,c,x,subst_gridData,subst_pairT,GaussianBinetReciprocalMean.subst_data,
      GaussianBinetStirlingUnitDifferenceAlgebra.subst_coefficient,ConciseIPRA.PTm.subst_zero] using
      (tag_identity (s A) (s B) (s D) (s sign) (s M) (var 0) hs hm).eqTrans right.eqSymm
  have sum_read := (GaussianRationalFiniteSum.sum_congr_bounded rowBody affineBody M _ _ rows_eq).eqTrans (affine_sum c x M)
  have constantScaled : Γ ⊢[PRAAx] qmul w (natScale M v) ≐ v :=
    (qmul_congr (.eqRefl w) (natScale_as_product M v)).eqTrans
      ((qmul_associative w (naturalPoint M) v).eqSymm.eqTrans
        ((qmul_congr ((qmul_commutative w (naturalPoint M)).eqTrans
          ((natScale_as_product M w).eqSymm.eqTrans (weight_sum_one M hM))) (.eqRefl v)).eqTrans
          ((qmul_commutative qone v).eqTrans (qmul_one_right v (qnegative_canonical _)))))
  have mainScaled : Γ ⊢[PRAAx] qmul w (qmul c u) ≐ qmul c (qmul w u) :=
    GaussianRationalPowerAlgebra.commute_nested w c u
  exact (qmul_congr (.eqRefl w) sum_read).eqTrans
    ((GaussianRationalCoefficientScaling.qmul_add w (qmul c u) (natScale M v)).eqTrans
      (qadd_congr mainScaled constantScaled))

theorem actual_weighted_resolvent_unit_grid_identity_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
        value (var 0) (var 1) (var 2) (var 3) (var 4) ≐
          qsub (qmul (coefficient (var 0) (var 1) (var 2) (var 3))
            (GaussianBinetReciprocalMean.value (var 0) (var 1) (var 2) (var 3) zero (var 4))) qone) :=
  closeUniv 5 (.impI (.impI (finite_identity _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedResolventGrid
