import IPRADerivations.Analysis.Euler.Logarithms.LowerBounds.GaussianEulerLogarithmicLowerGuardBound
import IPRADerivations.Analysis.Euler.Logarithms.UpperBounds.GaussianEulerLogarithmicUpperCutoffBudget
import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianEulerLogarithmicCommonCutoff

/-!
# Both actual logarithmic tails at the common expanded cutoffs

The lower and upper data are the literal original compact names in the
three-piece partition with geometry (2A,R+j) and evaluator client R,j.
The exact index shift aligns the proved lower bound without changing R.
Both observations satisfy the same dyadic budget at every later cutoff;
equal cutoffs use the actual zero-width upper observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCommonTails

open_ipra
open GaussianEulerLogarithmicIntervalName (nameF data)
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData)
open GaussianEulerLogarithmicMultiplier (lipschitz)
open GaussianEulerLogarithmicCommonCutoff (cutoff lowerIndex)
open GaussianEulerLogarithmicLowerRootRows (panelDegree intervalDen degree_identity)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive top_positive)
open GaussianGammaCompactCutoffGeometry (lowerWidth upperWidth delta)
open GaussianRationalMetric (bounded)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalReciprocal (bound_congr)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev source (z R B A : PTm n) : Fm PTm n := GaussianEulerLowerPowerCoefficients.source z R B A
def lowerData (j z R B A k l : PTm n) : PTm n := data j z R B one (lowerWidth k l (two*A))
  (etaDen l (two*A) (R+j)) (top l (two*A) (R+j))
def upperData (j z R B A k l : PTm n) : PTm n := data j z R B
  (etaDen l (two*A) (R+j)*top k (two*A) (R+j)) (upperWidth k l (two*A) (R+j))
  (etaDen l (two*A) (R+j)) (top l (two*A) (R+j))

private theorem data_congr (j z R B a C E T a' C' E' T' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hc : Γ ⊢[PRAAx] C ≐ C')
    (he : Γ ⊢[PRAAx] E ≐ E') (ht : Γ ⊢[PRAAx] T ≐ T') : Γ ⊢[PRAAx]
    data j z R B a C E T ≐ data j z R B a' C' E' T' := by
  have first : Γ ⊢[PRAAx] data j z R B a C E T ≐ data j z R B a' C E T := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0)
        (Syn.shift C) (Syn.shift E) (Syn.shift T)) ha
  have second : Γ ⊢[PRAAx] data j z R B a' C E T ≐ data j z R B a' C' E T := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a')
        (var 0) (Syn.shift E) (Syn.shift T)) hc
  have third : Γ ⊢[PRAAx] data j z R B a' C' E T ≐ data j z R B a' C' E' T := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a')
        (Syn.shift C') (var 0) (Syn.shift T)) he
  have fourth : Γ ⊢[PRAAx] data j z R B a' C' E' T ≐ data j z R B a' C' E' T' := by
    simpa only [GaussianEulerLogarithmicIntervalName.subst_data,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift a')
        (Syn.shift C') (Syn.shift E') (var 0)) ht
  exact first.eqTrans (second.eqTrans (third.eqTrans fourth))

theorem lower_data_shift (j z R B A k l : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicLowerGuardBound.data j z R B (lowerIndex k R j) (lowerIndex l R j) A (top l (two*A) (R+j)) ≐
      lowerData j z R B A k l := by
  let K := lowerIndex k R j
  let L := lowerIndex l R j
  have degree : Γ ⊢[PRAAx] panelDegree A ≐ two*A := (degree_identity A hA).eqSymm
  have width : Γ ⊢[PRAAx] lowerWidth K L (panelDegree A) ≐ lowerWidth k l (two*A) :=
    (congrMonus (congrAp2 powF (congrMul degree (.eqRefl (delta K L))) (.eqRefl two)) (.eqRefl one)).eqTrans
      (GaussianEulerLogarithmicCommonCutoff.lower_width_shift k l A R j)
  have eta : Γ ⊢[PRAAx] intervalDen L A R ≐ etaDen l (two*A) (R+j) := by
    have heights : Γ ⊢[PRAAx] GaussianGammaIntegralCutoffs.height L (panelDegree A) R ≐
        GaussianGammaIntegralCutoffs.height L (two*A) R :=
      congrAdd (congrAdd (congrAdd (.eqRefl L) degree) (.eqRefl (GaussianGammaIntegralCutoffs.tailCoefficient R))) (.eqRefl (num 10))
    have first : Γ ⊢[PRAAx] etaDen L (panelDegree A) R ≐ etaDen L (two*A) R :=
      congrAp2 powF (congrMul degree heights) (.eqRefl two)
    exact first.eqTrans (GaussianEulerLogarithmicCommonCutoff.eta_shift l A R j)
  exact data_congr j z R B one (lowerWidth K L (panelDegree A)) (intervalDen L A R) (top l (two*A) (R+j))
    one (lowerWidth k l (two*A)) (etaDen l (two*A) (R+j)) (top l (two*A) (R+j)) (.eqRefl _) width eta (.eqRefl _)

theorem lower_bound (p r j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hc : Γ ⊢[PRAAx] le (cutoff r j A) k) (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (lowerData j z R B A k l)) (unit p+unit (r+num 6)) (unit (r+num 6)*unit p) := by
  have old : Γ ⊢[PRAAx] bounded
      (ap2 nameF p (GaussianEulerLogarithmicLowerGuardBound.data j z R B (lowerIndex k R j) (lowerIndex l R j) A (top l (two*A) (R+j))))
      (unit p+unit (r+num 6)) (unit (r+num 6)*unit p) :=
    GaussianEulerLogarithmicLowerGuardBound.original_cutoff_tail_bound p j z R B r
      (lowerIndex k R j) (lowerIndex l R j) A (top l (two*A) (R+j)) h
      (GaussianEulerLogarithmicCommonCutoff.cutoff_pays_lower r k j A R hc)
      (GaussianEulerLogarithmicCommonCutoff.later_lower_index k l R j hkl) (top_positive l (two*A) (R+j))
  have same : Γ ⊢[PRAAx]
      ap2 nameF p (GaussianEulerLogarithmicLowerGuardBound.data j z R B (lowerIndex k R j) (lowerIndex l R j) A (top l (two*A) (R+j))) ≐
        ap2 nameF p (lowerData j z R B A k l) :=
    congrAp2 nameF (.eqRefl p) (lower_data_shift j z R B A k l h.andE₁)
  exact bound_congr same (.eqRefl _) (.eqRefl _) old

theorem strict_upper_source (j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hkl : Γ ⊢[PRAAx] lt k l) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicUpperCutoffBudget.source j z R B k (two*A) (upperWidth k l (two*A) (R+j))
      (etaDen l (two*A) (R+j)) (top l (two*A) (R+j)) := by
  let E := etaDen l (two*A) (R+j)
  let K := top k (two*A) (R+j)
  let C := upperWidth k l (two*A) (R+j)
  let T := top l (two*A) (R+j)
  have he := eta_den_positive (Γ := Γ) l (two*A) (R+j)
  have start : Γ ⊢[PRAAx] le E (K*E) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right E (top_positive k (two*A) (R+j)))
  have endpoint : Γ ⊢[PRAAx] K*E+C ≐ E*T :=
    (by dsimp only [K,E,C,upperWidth]; ipra_ring : Γ ⊢[PRAAx] K*E+C ≐ E*(K+two*delta k l)).eqTrans
      (congrMul (.eqRefl E) (GaussianGammaCompactCutoffGeometry.top_refinement k l (two*A) (R+j) (le_of_lt hkl)).eqSymm)
  exact .andI (.andI (.andI h.andE₂.andE₁.andE₁ (.andI he h.andE₂.andE₁.andE₂))
    (.andI start (le_congr endpoint.eqSymm (.eqRefl _) (le_refl (E*T)))))
    (GaussianGammaCompactCutoffGeometry.upper_positive k l (two*A) (R+j) hkl)

theorem strict_upper_bound (p r j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hc : Γ ⊢[PRAAx] le (cutoff r j A) k) (hkl : Γ ⊢[PRAAx] lt k l) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (upperData j z R B A k l)) (unit p+unit (r+num 6)) (unit (r+num 6)*unit p) := by
  let E := etaDen l (two*A) (R+j)
  let C := upperWidth k l (two*A) (R+j)
  let T := top l (two*A) (R+j)
  have old := GaussianEulerLogarithmicUpperCutoffBudget.original_cutoff_tail_bound p j z R B k (two*A) C E T
    (strict_upper_source j z R B A k l h hkl)
  have index := le_trans (GaussianEulerLogarithmicCommonCutoff.cutoff_later (Γ := Γ) r j A) hc
  have order := GaussianExponentialReference.unit_monotone (Γ := Γ) (add_le_add_right (num 6) index)
  have compare : Γ ⊢[PRAAx] le ((unit p+unit (k+num 6))*(unit (r+num 6)*unit p))
      ((unit p+unit (r+num 6))*(unit (k+num 6)*unit p)) := by
    ipra_le (𝔞(unit p)*𝔞(unit p))*sl order
  have reduced : Γ ⊢[PRAAx] bounded (GaussianEulerLogarithmicUpperCutoffBudget.point p j z R B k (two*A) C E T)
      (unit p+unit (r+num 6)) (unit (r+num 6)*unit p) :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ (unit_positive (k+num 6)) (unit_positive p))
      (positive_product _ _ (unit_positive (r+num 6)) (unit_positive p)) compare old
  have sameData : Γ ⊢[PRAAx] data j z R B (top k (two*A) (R+j)*E) C E T ≐ upperData j z R B A k l :=
    data_congr j z R B (top k (two*A) (R+j)*E) C E T (E*top k (two*A) (R+j)) C E T
      (mul_comm _ _) (.eqRefl _) (.eqRefl _) (.eqRefl _)
  have same : Γ ⊢[PRAAx] GaussianEulerLogarithmicUpperCutoffBudget.point p j z R B k (two*A) C E T ≐
      ap2 nameF p (upperData j z R B A k l) := congrAp2 nameF (.eqRefl p) sameData
  exact bound_congr same (.eqRefl _) (.eqRefl _) reduced

theorem upper_zero (p j z R B A k l : PTm n) (hkl : Γ ⊢[PRAAx] k ≐ l) : Γ ⊢[PRAAx]
    ap2 nameF p (upperData j z R B A k l) ≐ qzero := by
  let E := etaDen l (two*A) (R+j)
  let T := top l (two*A) (R+j)
  let a := E*top k (two*A) (R+j)
  have width : Γ ⊢[PRAAx] upperWidth k l (two*A) (R+j) ≐ zero := by
    have first : Γ ⊢[PRAAx] upperWidth k l (two*A) (R+j) ≐ upperWidth k k (two*A) (R+j) := by
      ipra_congr (upperWidth (var 0) (var 1) (var 2) (var 3) : PTm 4) with
        [.eqRefl k, hkl.eqSymm, .eqRefl (two*A), .eqRefl (R+j)]
    exact first.eqTrans (GaussianGammaCompactCutoffGeometry.same_upper k (two*A) (R+j))
  have sameData : Γ ⊢[PRAAx] upperData j z R B A k l ≐ data j z R B a zero E T :=
    data_congr j z R B a (upperWidth k l (two*A) (R+j)) E T a zero E T (.eqRefl _) width (.eqRefl _) (.eqRefl _)
  exact (congrAp2 nameF (.eqRefl p) sameData).eqTrans
    (GaussianCompactZeroWidth.observation_zero evaluatorF p a E (lipschitz j R E T) T (fixedData j R E T z B)
      (eta_den_positive l (two*A) (R+j)))

theorem upper_bound (p r j z R B A k l : PTm n) (h : Γ ⊢[PRAAx] source z R B A)
    (hc : Γ ⊢[PRAAx] le (cutoff r j A) k) (hkl : Γ ⊢[PRAAx] le k l) : Γ ⊢[PRAAx]
    bounded (ap2 nameF p (upperData j z R B A k l)) (unit p+unit (r+num 6)) (unit (r+num 6)*unit p) :=
  .orE (lt_or_eq_of_le hkl) (strict_upper_bound p r j z R B A k l h.wk hc.wk Prf.hyp0)
    (bound_congr (upper_zero p j z R B A k l Prf.hyp0).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerNamedUpperTail.zero_bound (unit p+unit (r+num 6)) (unit (r+num 6)*unit p)
        (positive_product _ _ (unit_positive (r+num 6)) (unit_positive p))))

theorem actual_common_logarithmic_tail_pair_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((source (var 3) (var 4) (var 5) (var 6) ⋏
      (le (cutoff (var 1) (var 2) (var 6)) (var 7) ⋏ le (var 7) (var 8))) ⟶
      (bounded (ap2 nameF (var 0) (lowerData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (unit (var 0)+unit (var 1+num 6)) (unit (var 1+num 6)*unit (var 0)) ⋏
       bounded (ap2 nameF (var 0) (upperData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8)))
        (unit (var 0)+unit (var 1+num 6)) (unit (var 1+num 6)*unit (var 0)))) :=
  closeUniv 9 (.impI (.andI
    (lower_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)
    (upper_bound _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicCommonTails
