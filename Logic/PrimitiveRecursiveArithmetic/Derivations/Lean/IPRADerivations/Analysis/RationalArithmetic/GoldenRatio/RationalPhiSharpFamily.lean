import IPRADerivations.Analysis.Polynomials.Products.RationalPolynomialPowers
import IPRADerivations.Analysis.RationalArithmetic.GoldenRatio.RationalPhiSharpness

/-!
# The literal general-Q sharp superelliptic family

For the original rational buffer Q of width s+1, construct
Q(X)^r + product_(j=1)^m (X-j) and the actual points (j,Q(j)).
The leading term survives because r*s<m. The same original point codes
lie on the curve and on the feature hyperplane y-Q(x)=0. This is a
sharpness family, not a quantitative proper-subspace cover theorem.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalPhiSharpFamily

open_ipra
open RationalPolynomialGaussianEmbedding (evaluate hornerF embed_congr)
open RationalPolynomialBuffersGaussianEmbedding (leftPad pad_length pad_lookup pad_coefficient_before pad_evaluation added added_length added_lookup added_evaluation)
open RationalConsecutiveFactorProduct (consecutive root consecutive_length consecutive_head consecutive_root)
open RationalGaussianEmbedding (embed scalarZero scalarOne embed_equal embed_zero embed_add embed_canonical rational_equal_of_embed)
open RationalArgmin (rationalEq rationalEq_congr)
open RationalPhiSectionNonzero (curveInput)
open RationalSuperellipticNormDegree (pointPowers)
open RationalCurvePointsGaussianEmbedding (distinct)
open GaussianRationalFiberGrouping (abscissa ordinate)
open GaussianRationalHorner (qzero qadd canonical)
open GaussianRationalSyntheticDivision (qone qadd_congr qzero_add)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def powered (Q s r m : PTm n) : PTm n := leftPad (RationalPolynomialPowers.power Q s r) (monus m (r*s))
def polynomial (Q s r m : PTm n) : PTm n := added (powered Q s r m) (consecutive m) (succ m)
def pointBody : PTm 2 := pairT (root (var 0)) (evaluate (var 1) (root (var 0)))
def points (Q m : PTm n) : PTm n := sequence pointBody m Q

ipra_subst powered
ipra_subst polynomial
ipra_subst points

theorem powered_length (Q s r m : PTm n) (hm : Γ ⊢[PRAAx] le (r*s) m) : Γ ⊢[PRAAx] length (powered Q s r m) ≐ succ m :=
  (pad_length _ _).eqTrans ((congrAdd (.eqRefl _) (RationalPolynomialPowers.power_length Q s r)).eqTrans
    ((add_succ _ _).eqTrans (congrSucc ((add_comm _ _).eqTrans (eq_add_of_le hm).eqSymm))))
theorem polynomial_length (Q s r m : PTm n) : Γ ⊢[PRAAx] length (polynomial Q s r m) ≐ succ m := added_length _ _ _
theorem powered_head_zero (Q s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx] entry (powered Q s r m) zero ≐ scalarZero := by
  have split : Γ ⊢[PRAAx] m ≐ r*s+succ (monus m (succ (r*s))) := (eq_add_of_le hm).eqTrans (by ipra_ring)
  have gap := (congrMonus split (.eqRefl (r*s))).eqTrans (add_monus' (succ (monus m (succ (r*s)))) (r*s))
  have positive : Γ ⊢[PRAAx] lt zero (monus m (r*s)) := le_congr (.eqRefl _) gap.eqSymm (zero_lt_succ _)
  have stored : Γ ⊢[PRAAx] lt zero (monus m (r*s)+length (RationalPolynomialPowers.power Q s r)) :=
    lt_congr (.eqRefl _) (pad_length _ _) (lt_congr (.eqRefl _) (powered_length Q s r m (le_of_lt hm)).eqSymm (zero_lt_succ m))
  exact (pad_lookup _ _ _ stored).eqTrans (pad_coefficient_before _ _ _ positive)
theorem polynomial_head (Q s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx] embed (entry (polynomial Q s r m) zero) ≐ qone :=
  (embed_congr (added_lookup _ _ _ _ (zero_lt_succ m))).eqTrans ((embed_add _ _).eqTrans
    ((qadd_congr ((embed_congr (powered_head_zero Q s r m hm)).eqTrans embed_zero) (consecutive_head m)).eqTrans
      (qzero_add _ GaussianRationalSyntheticDivision.qone_canonical)))

theorem polynomial_evaluation (Q s r m x : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) (hm : Γ ⊢[PRAAx] le (r*s) m) : Γ ⊢[PRAAx]
    embed (evaluate (polynomial Q s r m) x) ≐ qadd
      (embed (RationalScalarPowerGaussianEmbedding.power (evaluate Q x) r)) (embed (evaluate (consecutive m) x)) :=
  (embed_congr (added_evaluation _ _ _ _ (powered_length Q s r m hm) (consecutive_length m))).eqTrans
    ((embed_add _ _).eqTrans (qadd_congr (embed_congr ((pad_evaluation _ _ _).eqTrans (RationalPolynomialPowers.power_evaluation Q s r x hQ))) (.eqRefl _)))

theorem polynomial_head_nonzero (Q s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx]
    neg (rationalEq (entry (polynomial Q s r m) zero) scalarZero) :=
  .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero ((polynomial_head Q s r m hm).wk.eqSymm.eqTrans
    ((embed_equal _ _ Prf.hyp0).eqTrans embed_zero)))
theorem curve_input (Q s r m : PTm n) (hr : Γ ⊢[PRAAx] le one r) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx]
    curveInput (polynomial Q s r m) s r m := .andI hr (.andI (polynomial_length Q s r m) (.andI (polynomial_head_nonzero Q s r m hm) hm))

theorem polynomial_degree (Q s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx]
    RationalPolynomialDegreeGaussianEmbedding.degree (polynomial Q s r m) m ≐ m := by
  let C := polynomial Q s r m
  have nonzero : Γ ⊢[PRAAx] neg (RationalArithmetic.recode (entry C zero) ≐ scalarZero) := by
    refine .impI (.impE GaussianRationalCurveFibers.gaussian_one_nonzero ?_)
    exact (polynomial_head Q s r m hm).wk.eqSymm.eqTrans ((RationalGaussianEmbedding.embed_recode _).eqSymm.eqTrans
      ((embed_congr Prf.hyp0).eqTrans embed_zero))
  have bound := RationalPolynomialDegreeGaussianEmbedding.first_from_witness C m zero (zero_lt_succ m) nonzero
  have first : Γ ⊢[PRAAx] RationalPolynomialDegreeGaussianEmbedding.first C m ≐ zero := le_antisymm bound (zero_le _)
  exact (congrMonus (.eqRefl _) first).eqTrans (monus_zero _)

theorem points_length (Q m : PTm n) : Γ ⊢[PRAAx] length (points Q m) ≐ m := sequence_length _ _ _
theorem point_lookup (Q m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] entry (points Q m) j ≐ pairT (root j) (evaluate Q (root j)) := by
  simpa [points,pointBody,inst2] using sequence_decode (Γ := Γ) pointBody (x := Q) hj
theorem point_abscissa (Q m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] abscissa (points Q m) j ≐ root j :=
  (point_lookup Q m j hj).fstE
theorem point_ordinate (Q m j : PTm n) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] ordinate (points Q m) j ≐ evaluate Q (root j) :=
  (point_lookup Q m j hj).sndE

theorem points_distinct (Q m : PTm n) : Γ ⊢[PRAAx] distinct (points Q m) := by
  refine .allI (.impI (.allI (.impI (.impI (.impI ?_)))))
  let C := Syn.shift (Syn.shift Q)
  let M := Syn.shift (Syn.shift m)
  let F := rationalEq (abscissa (points C M) (var 0)) (abscissa (points C M) (var 1)) ⋏
    rationalEq (ordinate (points C M) (var 0)) (ordinate (points C M) (var 1))
  let Δ := F :: lt (var 1) (var 0) :: lt (var 0) (length (points C M)) :: lt (var 1) (length (points C M)) :: (Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt (var 1) M := lt_congr (.eqRefl _) (points_length C M) (.hyp (by simp [Δ]))
  have hj : Δ ⊢[PRAAx] lt (var 0) M := lt_congr (.eqRefl _) (points_length C M) (.hyp (by simp [Δ]))
  have eq := RationalPhiSharpness.root_injective (var 0) (var 1)
    (rationalEq_congr (point_abscissa C M (var 0) hj) (point_abscissa C M (var 1) hi) (.andE₁ Prf.hyp0))
  have bot : Δ ⊢[PRAAx] .bot := le_lt_absurd _ (le_congr (.eqRefl _) eq (le_refl (var 0))) Prf.hyp1
  simpa [Δ,F,C,M,Fm.shift,Syn.shift] using bot

theorem curve_point_at (Q s r m j : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) (hm : Γ ⊢[PRAAx] le (r*s) m)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] rationalEq
      (RationalScalarPowerGaussianEmbedding.power (ordinate (points Q m) j) r)
      (evaluate (polynomial Q s r m) (abscissa (points Q m) j)) := by
  have left := embed_congr (congrAp2 RationalScalarPowerGaussianEmbedding.powerF (.eqRefl r) (point_ordinate Q m j hj))
  have right := (embed_congr (RationalPolynomialPowers.evaluation_congr (.eqRefl (polynomial Q s r m)) (point_abscissa Q m j hj))).eqTrans
    ((polynomial_evaluation Q s r m (root j) hQ hm).eqTrans
      ((qadd_congr (.eqRefl _) ((embed_equal _ _ (consecutive_root j m hj)).eqTrans embed_zero)).eqTrans
        (GaussianReciprocalHorner.qadd_zero_right _ (embed_canonical _))))
  exact rational_equal_of_embed _ _ (left.eqTrans right.eqSymm)

theorem points_on_curve (Q s r m : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) (hm : Γ ⊢[PRAAx] le (r*s) m) : Γ ⊢[PRAAx]
    pointPowers (polynomial Q s r m) r (points Q m) := by
  refine .allI (.impI ?_)
  let a := Syn.shift Q
  let b := Syn.shift s
  let c := Syn.shift r
  let M := Syn.shift m
  let Δ := lt (var 0) (length (points a M)) :: Γ.map Fm.shift
  have hh : Δ ⊢[PRAAx] length a ≐ succ b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hQ.shift.wk
  have mh : Δ ⊢[PRAAx] le (c*b) M := by simpa [Δ,b,c,M,Fm.shift,Syn.shift] using hm.shift.wk
  simpa [Δ,a,b,c,M,Fm.shift,Syn.shift] using curve_point_at a b c M (var 0) hh mh
    (lt_congr (.eqRefl _) (points_length a M) Prf.hyp0)

/-- Coefficients are ascending in the source feature vector; the last
coordinate is one. The original Q buffer remains descending. -/
def lambdaCoefficient (Q s k : PTm n) : PTm n := Foundations.GuardedTotalization.sel (eqb k (succ s)) scalarOne
  (RationalArithmetic.negative (entry Q (monus s k)))
def lambdaBody : PTm 2 := lambdaCoefficient (fstT (var 1)) (sndT (var 1)) (var 0)
def hyperplane (Q s : PTm n) : PTm n := sequence lambdaBody (RationalPhiFeatures.dimension s) (pairT Q s)
ipra_subst lambdaCoefficient [Foundations.GuardedTotalization.sel]
ipra_subst hyperplane

theorem lambda_coefficient_congr {Q P s t i j : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ P) (hs : Γ ⊢[PRAAx] s ≐ t) (hi : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] lambdaCoefficient Q s i ≐ lambdaCoefficient P t j := by
  ipra_congr (lambdaCoefficient (var 0) (var 1) (var 2) : PTm 3) with [hQ, hs, hi]
theorem lambda_body_at (Q s k : PTm n) : Γ ⊢[PRAAx] inst2 lambdaBody k (pairT Q s) ≐ lambdaCoefficient Q s k := by
  simpa only [lambdaBody,inst2,subst_lambdaCoefficient,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    lambda_coefficient_congr (fst_pair (Γ := Γ) Q s) (snd_pair Q s) (.eqRefl k)
theorem hyperplane_length (Q s : PTm n) : Γ ⊢[PRAAx] length (hyperplane Q s) ≐ RationalPhiFeatures.dimension s := sequence_length _ _ _
theorem hyperplane_lookup (Q s k : PTm n) (hk : Γ ⊢[PRAAx] lt k (RationalPhiFeatures.dimension s)) : Γ ⊢[PRAAx]
    entry (hyperplane Q s) k ≐ lambdaCoefficient Q s k :=
  (sequence_decode lambdaBody (x := pairT Q s) hk).eqTrans (lambda_body_at Q s k)
theorem hyperplane_last (Q s : PTm n) : Γ ⊢[PRAAx] entry (hyperplane Q s) (succ s) ≐ scalarOne :=
  (hyperplane_lookup Q s (succ s) (le_refl _)).eqTrans (Foundations.GuardedTotalization.sel_one (eqb_of_eq (.eqRefl _)))
theorem hyperplane_old (Q s k : PTm n) (hk : Γ ⊢[PRAAx] le k s) : Γ ⊢[PRAAx]
    entry (hyperplane Q s) k ≐ RationalArithmetic.negative (entry Q (monus s k)) := by
  have bound : Γ ⊢[PRAAx] lt k (RationalPhiFeatures.dimension s) :=
    le_trans ((succ_monus_succ k s).eqTrans hk) (le_succ_self (succ s))
  have ne : Γ ⊢[PRAAx] neg (k ≐ succ s) := .impI (not_succ_le_self s Fm.bot (le_congr Prf.hyp0 (.eqRefl _) hk.wk))
  exact (hyperplane_lookup Q s k bound).eqTrans (Foundations.GuardedTotalization.sel_zero (eqb_of_ne ne))

theorem hyperplane_nonzero (Q s : PTm n) : Γ ⊢[PRAAx] RationalPhiSectionZero.nonzero (hyperplane Q s) s := by
  refine .exI (succ s) ?_
  have ne : Γ ⊢[PRAAx] neg (rationalEq (entry (hyperplane Q s) (succ s)) scalarZero) :=
    .impI (.impE RationalPhiSection.unit_nonzero (rationalEq_congr (hyperplane_last Q s).wk (.eqRefl _) Prf.hyp0))
  simpa [RationalPhiSectionZero.nonzero,RationalPhiFeatures.dimension,lt] using Prf.andI (le_refl (succ (succ s))) ne

theorem hyperplane_polynomial_entry (Q s k : PTm n) (hk : Γ ⊢[PRAAx] le k s) : Γ ⊢[PRAAx]
    embed (entry (RationalPhiFeatures.polynomial (hyperplane Q s) s) k) ≐ GaussianRationalMetric.qnegative (embed (entry Q k)) :=
  (embed_congr (RationalPhiFeatures.polynomial_lookup _ _ _ hk)).eqTrans ((RationalGaussianEmbedding.embed_recode _).eqTrans
    ((embed_congr (hyperplane_old Q s (monus s k) (GaussianRationalMonicReconstruction.monus_le_left s k))).eqTrans
      ((RationalGaussianEmbedding.embed_negative _).eqTrans (RationalGaussianEmbedding.negative_congr
        (embed_congr (Foundations.SequenceComposition.entry_congr (.eqRefl Q) (GaussianRationalMonicReconstruction.complement s k hk)))))))

theorem hyperplane_polynomial_evaluation (Q s x : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) : Γ ⊢[PRAAx]
    embed (evaluate (RationalPhiFeatures.polynomial (hyperplane Q s) s) x) ≐ GaussianRationalMetric.qnegative (embed (evaluate Q x)) := by
  let C := RationalPolynomialGaussianEmbedding.coefficients Q (succ s)
  let D := RationalSectionCollapse.negativePolynomial C
  have entries : Γ ⊢[PRAAx] RationalPolynomialBuffersGaussianEmbedding.embeddedEntries
      (RationalPhiFeatures.polynomial (hyperplane Q s) s) D (succ s) := by
    refine .allI (.impI ?_)
    let a := Syn.shift Q
    let b := Syn.shift s
    let Δ := lt (var 0) (succ b) :: Γ.map Fm.shift
    have kk : Δ ⊢[PRAAx] le (var 0) b := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have bound : Δ ⊢[PRAAx] lt (var 0) (length (RationalPolynomialGaussianEmbedding.coefficients a (succ b))) :=
      lt_congr (.eqRefl _) (RationalPolynomialGaussianEmbedding.coefficients_length _ _).eqSymm Prf.hyp0
    have high := (GaussianRationalCoefficientScaling.scaled_lookup (RationalPolynomialGaussianEmbedding.coefficients a (succ b))
      GaussianRationalMatrixFiniteSums.minusOne (var 0) bound).eqTrans
        ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) (RationalPolynomialGaussianEmbedding.coefficient_lookup a (succ b) (var 0) Prf.hyp0)).eqTrans
          (GaussianRationalMatrixFiniteSums.negative_as_minusOne _).eqSymm)
    simpa [Δ,a,b,C,D,Fm.shift,Syn.shift,RationalSectionCollapse.negativePolynomial] using
      (hyperplane_polynomial_entry a b (var 0) kk).eqTrans high.eqSymm
  have dl : Γ ⊢[PRAAx] length D ≐ succ s := (GaussianRationalCoefficientScaling.scaled_length _ _).eqTrans
    (RationalPolynomialGaussianEmbedding.coefficients_length _ _)
  exact (RationalPolynomialBuffersGaussianEmbedding.evaluation_transport _ _ _ x (RationalPhiFeatures.polynomial_length _ _) dl entries).eqTrans
    ((RationalSectionCollapse.negative_evaluation C (embed x)).eqTrans
      (RationalGaussianEmbedding.negative_congr (RationalPolynomialBuffersGaussianEmbedding.evaluation_at_width Q (succ s) x hQ).eqSymm))

theorem hyperplane_equation (Q s x : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) : Γ ⊢[PRAAx]
    RationalPhiFeatures.equation (hyperplane Q s) s x (evaluate Q x) ≐ scalarZero := by
  let q := embed (evaluate Q x)
  have last := (embed_congr (hyperplane_last (Γ := Γ) Q s)).eqTrans RationalGaussianEmbedding.embed_one
  have product := (RationalGaussianEmbedding.embed_multiply (Γ := Γ) (entry (hyperplane Q s) (succ s)) (evaluate Q x)).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr last (.eqRefl _)).eqTrans
      ((GaussianRationalFiniteProduct.raw_one_left q).eqTrans (GaussianTranslatedNonconstant.recode_eq _ (embed_canonical _))))
  have e := (embed_add (Γ := Γ) (evaluate (RationalPhiFeatures.polynomial (hyperplane Q s) s) x)
    (RationalArithmetic.multiply (entry (hyperplane Q s) (succ s)) (evaluate Q x))).eqTrans
      ((qadd_congr (hyperplane_polynomial_evaluation Q s x hQ) product).eqTrans
        ((GaussianReciprocalHorner.qadd_commutative _ _).eqTrans (GaussianCoefficientNormOrder.qsub_self q)))
  exact RationalPolynomialBuffersGaussianEmbedding.canonical_equal_of_embedding _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one)) (e.eqTrans embed_zero.eqSymm)

theorem points_on_hyperplane (Q s m : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) : Γ ⊢[PRAAx]
    RationalPhiSectionNonzero.lineEquations (hyperplane Q s) s (points Q m) := by
  refine .allI (.impI ?_)
  let a := Syn.shift Q
  let b := Syn.shift s
  let M := Syn.shift m
  let Δ := lt (var 0) (length (points a M)) :: Γ.map Fm.shift
  have hj : Δ ⊢[PRAAx] lt (var 0) M := lt_congr (.eqRefl _) (points_length a M) Prf.hyp0
  have hh : Δ ⊢[PRAAx] length a ≐ succ b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hQ.shift.wk
  have args : Δ ⊢[PRAAx] RationalPhiFeatures.equation (hyperplane a b) b (abscissa (points a M) (var 0)) (ordinate (points a M) (var 0)) ≐
      RationalPhiFeatures.equation (hyperplane a b) b (root (var 0)) (evaluate a (root (var 0))) := by
    ipra_congr (RationalPhiFeatures.equation (var 0) (var 1) (var 2) (var 3) : PTm 4) with
      [.eqRefl (hyperplane a b), .eqRefl b, point_abscissa a M (var 0) hj, point_ordinate a M (var 0) hj]
  simpa [Δ,a,b,M,Fm.shift,Syn.shift] using args.eqTrans (hyperplane_equation a b (root (var 0)) hh)

theorem point_dot_zero (Q s m j : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx]
    RationalPhiFeatures.dot (hyperplane Q s) s (abscissa (points Q m) j) (ordinate (points Q m) j) ≐ scalarZero := by
  have lines := points_on_hyperplane Q s m hQ
  have rule : Γ ⊢[PRAAx] lt j (length (points Q m)) ⟶
      RationalPhiFeatures.equation (hyperplane Q s) s (abscissa (points Q m) j) (ordinate (points Q m) j) ≐ scalarZero := by
    simpa [RationalPhiSectionNonzero.lineEquations] using lines.allE j
  exact (RationalPhiFeatures.dot_identity _ _ _ _).eqTrans (.impE rule (lt_congr (.eqRefl _) (points_length Q m).eqSymm hj))
theorem points_dot (Q s m : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) : Γ ⊢[PRAAx]
    RationalPhiSection.dotEquations (hyperplane Q s) s (points Q m) := by
  refine .allI (.impI ?_)
  let a := Syn.shift Q
  let b := Syn.shift s
  let M := Syn.shift m
  let Δ := lt (var 0) (length (points a M)) :: Γ.map Fm.shift
  have hh : Δ ⊢[PRAAx] length a ≐ succ b := by simpa [Δ,a,b,Fm.shift,Syn.shift] using hQ.shift.wk
  have code := point_dot_zero a b M (var 0) hh (lt_congr (.eqRefl _) (points_length a M) Prf.hyp0)
  have original := rational_equal_of_embed _ _ (embed_congr code)
  simpa [Δ,a,b,M,Fm.shift,Syn.shift] using original

/-- Exact original source sharp-family assertion, with actual buffers and
point/vector codes throughout. Quantitative cover existence is separate. -/
def certificate (Q s r m : PTm n) : Fm PTm n :=
  curveInput (polynomial Q s r m) s r m ⋏
    (RationalPolynomialDegreeGaussianEmbedding.degree (polynomial Q s r m) m ≐ m ⋏
      (length (points Q m) ≐ m ⋏ (distinct (points Q m) ⋏
        (pointPowers (polynomial Q s r m) r (points Q m) ⋏
          (length (hyperplane Q s) ≐ RationalPhiFeatures.dimension s ⋏
            (RationalPhiSectionZero.nonzero (hyperplane Q s) s ⋏ RationalPhiSection.dotEquations (hyperplane Q s) s (points Q m)))))))

theorem sharp_family (Q s r m : PTm n) (hQ : Γ ⊢[PRAAx] length Q ≐ succ s) (hr : Γ ⊢[PRAAx] le one r)
    (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx] certificate Q s r m :=
  .andI (curve_input Q s r m hr hm) (.andI (polynomial_degree Q s r m hm) (.andI (points_length Q m)
    (.andI (points_distinct Q m) (.andI (points_on_curve Q s r m hQ (le_of_lt hm))
      (.andI (hyperplane_length Q s) (.andI (hyperplane_nonzero Q s) (points_dot Q s m hQ)))))))

def output (Q s r m : PTm n) : PTm n := pairT (polynomial Q s r m) (pairT (points Q m)
  (pairT (hyperplane Q s) (RationalPolynomialDegreeGaussianEmbedding.degree (polynomial Q s r m) m)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (Q s r m : PTm n) : PTm n := app outputF ![Q,s,r,m]
ipra_subst output
theorem program_at (Q s r m : PTm n) : Γ ⊢[PRAAx] run Q s r m ≐ output Q s r m := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![Q,s,r,m]
theorem returned_polynomial (Q s r m : PTm n) : Γ ⊢[PRAAx] fstT (run Q s r m) ≐ polynomial Q s r m :=
  (program_at Q s r m).fstE
theorem returned_tail (Q s r m : PTm n) : Γ ⊢[PRAAx] sndT (run Q s r m) ≐ pairT (points Q m)
    (pairT (hyperplane Q s) (RationalPolynomialDegreeGaussianEmbedding.degree (polynomial Q s r m) m)) :=
  (program_at Q s r m).sndE
theorem returned_points (Q s r m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run Q s r m)) ≐ points Q m :=
  (returned_tail Q s r m).fstE
theorem returned_witness (Q s r m : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run Q s r m)) ≐ pairT (hyperplane Q s)
    (RationalPolynomialDegreeGaussianEmbedding.degree (polynomial Q s r m) m) :=
  (returned_tail Q s r m).sndE
theorem returned_hyperplane (Q s r m : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run Q s r m))) ≐ hyperplane Q s :=
  (returned_witness Q s r m).fstE
theorem returned_degree (Q s r m : PTm n) (hm : Γ ⊢[PRAAx] lt (r*s) m) : Γ ⊢[PRAAx] sndT (sndT (sndT (run Q s r m))) ≐ m :=
  (returned_witness Q s r m).sndE.eqTrans (polynomial_degree Q s r m hm)

theorem actual_general_q_sharp_family_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (length (var 0) ≐ succ (var 1) ⟶ le one (var 2) ⟶ lt (var 2*var 1) (var 3) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (.impI (.impI (sharp_family _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_general_q_sharp_polynomial_head_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2*var 1) (var 3) ⟶ embed (entry (polynomial (var 0) (var 1) (var 2) (var 3)) zero) ≐ qone) :=
  closeUniv 4 (.impI (polynomial_head _ _ _ _ Prf.hyp0))
theorem actual_general_q_sharp_point_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (length (var 0) ≐ succ (var 1) ⟶ le (var 2*var 1) (var 3) ⟶ lt (var 4) (var 3) ⟶
      rationalEq (RationalScalarPowerGaussianEmbedding.power (ordinate (points (var 0) (var 3)) (var 4)) (var 2))
        (evaluate (polynomial (var 0) (var 1) (var 2) (var 3)) (abscissa (points (var 0) (var 3)) (var 4)))) :=
  closeUniv 5 (.impI (.impI (.impI (curve_point_at _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_general_q_hyperplane_equation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (length (var 0) ≐ succ (var 1) ⟶ RationalPhiFeatures.equation (hyperplane (var 0) (var 1)) (var 1) (var 2) (evaluate (var 0) (var 2)) ≐ scalarZero) :=
  closeUniv 3 (.impI (hyperplane_equation _ _ _ Prf.hyp0))
theorem actual_general_q_sharp_family_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)
theorem actual_returned_general_q_sharp_degree_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (lt (var 2*var 1) (var 3) ⟶ sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3)))) ≐ var 3) :=
  closeUniv 4 (.impI (returned_degree _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalPhiSharpFamily
