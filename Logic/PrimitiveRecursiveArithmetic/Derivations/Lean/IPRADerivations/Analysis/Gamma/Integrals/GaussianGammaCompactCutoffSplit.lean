import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaCompactCutoffAlignment
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactZeroWidth

/-!
# Actual original compact Euler quadratures split at earlier cutoffs

The later original interval is partitioned on its actual later denominator.
Its middle name is genuinely aligned to the unchanged original earlier
eta/top name. All three resulting summands are actual compact names,
combined by the actual normalized addition programs. The equal-cutoff
case retains the two literal zero-width pieces.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaCompactCutoffSplit

open_ipra
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianGammaCompactCutoffGeometry (lowerWidth middleWidth upperWidth ratio)
open GaussianGammaCompactCutoffAlignment (middleData cross_data_congr)
open GaussianEulerCompactAdditivity (nameF intervalSource)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_to_diagonal)
open GaussianEuclideanDistanceName (pointCN)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R B p q A : PTm n) : Fm PTm n :=
  GaussianGammaEulerCompactQuadrature.source z R B ⋏ (le one A ⋏ le p q)
def lowerData (z R B p q A : PTm n) : PTm n := GaussianEulerCompactAdditivity.data z R B one
  (lowerWidth p q A) (etaDen q A R) (top q A R)
def upperData (z R B p q A : PTm n) : PTm n := GaussianEulerCompactAdditivity.data z R B (etaDen q A R*top p A R)
  (upperWidth p q A R) (etaDen q A R) (top q A R)
def rightData (z R B p q A : PTm n) : PTm n := GaussianEulerCompactAdditivity.data z R B (ratio p q A)
  (middleWidth p q A R+upperWidth p q A R) (etaDen q A R) (top q A R)
def tripleF : PR 2 := addF nameF (addF nameF nameF)
def geometricData (z R B p q A : PTm n) : PTm n := addData (lowerData z R B p q A)
  (addData (middleData z R B p q A) (upperData z R B p q A))
def splitData (z R B p q A : PTm n) : PTm n := addData (lowerData z R B p q A)
  (addData (GaussianGammaEulerCompactQuadrature.data z R B p A) (upperData z R B p q A))

ipra_subst source

ipra_subst lowerData [etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst upperData [etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst rightData [etaDen, top, GaussianGammaIntegralCutoffs.height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst geometricData
ipra_subst splitData

theorem euler_data_congr (z R B a C E T a' C' E' T' : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a')
    (hC : Γ ⊢[PRAAx] C ≐ C') (hE : Γ ⊢[PRAAx] E ≐ E') (hT : Γ ⊢[PRAAx] T ≐ T') : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.data z R B a C E T ≐ GaussianEulerCompactAdditivity.data z R B a' C' E' T' := by
  simpa using Prf.eqCongr
      (GaussianEulerCompactAdditivity.data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) : PTm 7)
      (σ := ![z,R,B,a,C,E,T]) (σ' := ![z,R,B,a',C',E',T']) (fun i => by
        fin_cases i
        · exact .eqRefl _
        · exact .eqRefl _
        · exact .eqRefl _
        · exact ha
        · exact hC
        · exact hE
        · exact hT)

theorem add_data_congr (x x' y y' : PTm n) (hx : Γ ⊢[PRAAx] x ≐ x') (hy : Γ ⊢[PRAAx] y ≐ y') : Γ ⊢[PRAAx]
    addData x y ≐ addData x' y' :=
  GaussianNameArithmetic.add_data_congr hx hy

theorem point_data_congr (f : PR 2) (x y : PTm n) (he : Γ ⊢[PRAAx] x ≐ y) (h : Γ ⊢[PRAAx] pointCN f x) : Γ ⊢[PRAAx] pointCN f y := by
  simpa using Prf.eqSubst (pointCN f (var 0) : Fm PTm 1) ![x] ![y] (fun i => by fin_cases i; exact he) (by simpa using h)

theorem piece_source (z R B p q A a C : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A)
    (ha : Γ ⊢[PRAAx] le one a) (he : Γ ⊢[PRAAx] le (a+C) (etaDen q A R*top q A R)) : Γ ⊢[PRAAx]
    intervalSource z R B a C (etaDen q A R) (top q A R) :=
  .andI (.andI h.andE₁.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive q A R) h.andE₁.andE₂)) (.andI ha he)

theorem upper_endpoint (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    etaDen q A R*top p A R+upperWidth p q A R ≐ etaDen q A R*top q A R :=
  (by unfold upperWidth; ipra_ring : Γ ⊢[PRAAx] etaDen q A R*top p A R+upperWidth p q A R ≐
    etaDen q A R*(top p A R+two*GaussianGammaCompactCutoffGeometry.delta p q)).eqTrans
      (congrMul (.eqRefl _) (GaussianGammaCompactCutoffGeometry.top_refinement p q A R h).eqSymm)

theorem right_endpoint (p q A R : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx]
    ratio p q A+(middleWidth p q A R+upperWidth p q A R) ≐ etaDen q A R*top q A R :=
  (add_assoc _ _ _).eqSymm.eqTrans ((congrAdd (GaussianGammaCompactCutoffGeometry.middle_endpoint p q A R h) (.eqRefl _)).eqTrans
    (upper_endpoint p q A R h))

theorem lower_source (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    intervalSource z R B one (lowerWidth p q A) (etaDen q A R) (top q A R) := by
  have bound := le_add_right (Γ := Γ) (one+lowerWidth p q A) (middleWidth p q A R+upperWidth p q A R)
  have endp := GaussianGammaCompactCutoffGeometry.three_endpoint p q A R h.andE₂.andE₂
  exact piece_source z R B p q A _ _ h (le_refl one) (le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx]
    (one+lowerWidth p q A)+(middleWidth p q A R+upperWidth p q A R) ≐ one+(lowerWidth p q A+middleWidth p q A R+upperWidth p q A R)).eqTrans endp) bound)

theorem middle_source (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    intervalSource z R B (ratio p q A) (middleWidth p q A R) (etaDen q A R) (top q A R) := by
  have later := mul_le_mul_right (etaDen q A R) (GaussianGammaCompactCutoffGeometry.top_monotone p q A R h.andE₂.andE₂)
  exact piece_source z R B p q A _ _ h (GaussianGammaCompactCutoffGeometry.ratio_positive p q A)
    (le_congr (GaussianGammaCompactCutoffGeometry.middle_endpoint p q A R h.andE₂.andE₂).eqSymm (by ipra_ring)
      (le_congr (by ipra_ring) (.eqRefl _) later))

theorem upper_source (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    intervalSource z R B (etaDen q A R*top p A R) (upperWidth p q A R) (etaDen q A R) (top q A R) :=
  piece_source z R B p q A _ _ h (GaussianRationalHorner.positive_product _ _
    (GaussianGammaIntegralCutoffs.eta_den_positive q A R) (GaussianGammaIntegralCutoffs.top_positive p A R))
    (le_congr (upper_endpoint p q A R h.andE₂.andE₂).eqSymm (.eqRefl _) (le_refl _))

theorem right_source (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    intervalSource z R B (ratio p q A) (middleWidth p q A R+upperWidth p q A R) (etaDen q A R) (top q A R) :=
  piece_source z R B p q A _ _ h (GaussianGammaCompactCutoffGeometry.ratio_positive p q A)
    (le_congr (right_endpoint p q A R h.andE₂.andE₂).eqSymm (.eqRefl _) (le_refl _))

theorem lower_regular (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx] pointCN nameF (lowerData z R B p q A) :=
  GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ (lower_source z R B p q A h)
theorem middle_regular (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx] pointCN nameF (middleData z R B p q A) :=
  GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ (middle_source z R B p q A h)
theorem upper_regular (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx] pointCN nameF (upperData z R B p q A) :=
  GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ (upper_source z R B p q A h)
theorem right_regular (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx] pointCN nameF (rightData z R B p q A) :=
  GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ (right_source z R B p q A h)
theorem original_regular (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    pointCN nameF (GaussianGammaEulerCompactQuadrature.data z R B p A) :=
  GaussianGammaEulerCompactQuadrature.fixed_interval_regular z R B p A h.andE₁

theorem strict_geometric_split (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    crossEquivalent nameF tripleF (GaussianGammaEulerCompactQuadrature.data z R B q A) (geometricData z R B p q A) := by
  let l := lowerWidth p q A
  let m := middleWidth p q A R
  let u := upperWidth p q A R
  let E := etaDen q A R
  let T := top q A R
  have lp := GaussianGammaCompactCutoffGeometry.lower_positive p q A h.andE₂.andE₁ hpq
  have mp := GaussianGammaCompactCutoffGeometry.middle_positive (Γ := Γ) p q A R
  have up := GaussianGammaCompactCutoffGeometry.upper_positive p q A R hpq
  have endpoint : Γ ⊢[PRAAx] le (one+(l+(m+u))) (E*T) :=
    le_congr ((by ipra_ring : Γ ⊢[PRAAx] one+(l+(m+u)) ≐ one+(l+m+u)).eqTrans
      (GaussianGammaCompactCutoffGeometry.three_endpoint p q A R h.andE₂.andE₂)).eqSymm (.eqRefl _) (le_refl _)
  have firstSource : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B one l (m+u) E T :=
    .andI (piece_source z R B p q A _ _ h (le_refl one) endpoint) (.andI lp (le_trans mp (le_add_right m u)))
  have secondSource : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B (ratio p q A) m u E T :=
    .andI (right_source z R B p q A h) (.andI mp up)
  have first := GaussianEulerCompactAdditivity.name_additivity z R B one l (m+u) E T firstSource
  have leftEq : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.data z R B one (l+(m+u)) E T ≐ GaussianGammaEulerCompactQuadrature.data z R B q A :=
    euler_data_congr _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _)
      (((add_assoc l m u).eqSymm).eqTrans (GaussianGammaCompactCutoffGeometry.widths_total p q A R h.andE₂.andE₂)) (.eqRefl _) (.eqRefl _)
  have rightEq : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.addedData z R B one l (m+u) E T ≐ addData (lowerData z R B p q A) (rightData z R B p q A) :=
    add_data_congr _ _ _ _ (.eqRefl _) (euler_data_congr _ _ _ _ _ _ _ _ _ _ _
      (GaussianGammaCompactCutoffGeometry.lower_endpoint p q A) (.eqRefl _) (.eqRefl _) (.eqRefl _))
  have movedFirst := cross_data_congr _ _ _ _ _ _ leftEq rightEq first
  have second := GaussianEulerCompactAdditivity.name_additivity z R B (ratio p q A) m u E T secondSource
  have rightSecond : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.addedData z R B (ratio p q A) m u E T ≐
      addData (middleData z R B p q A) (upperData z R B p q A) :=
    add_data_congr _ _ _ _ (.eqRefl _) (euler_data_congr _ _ _ _ _ _ _ _ _ _ _
      (GaussianGammaCompactCutoffGeometry.middle_endpoint p q A R h.andE₂.andE₂) (.eqRefl _) (.eqRefl _) (.eqRefl _))
  have movedSecond := cross_data_congr _ _ _ _ _ _ (.eqRefl (rightData z R B p q A)) rightSecond second
  have proper := GaussianNameArithmetic.add_equivalent nameF nameF nameF (addF nameF nameF)
    (lowerData z R B p q A) (lowerData z R B p q A) (rightData z R B p q A) (addData (middleData z R B p q A) (upperData z R B p q A))
    (lower_regular z R B p q A h) (lower_regular z R B p q A h) (right_regular z R B p q A h)
    (GaussianNameArithmetic.add_fast _ _ _ _ (middle_regular z R B p q A h) (upper_regular z R B p q A h))
    (GaussianNameEquivalence.diagonal_refl _ _) (cross_to_diagonal _ _ _ _ movedSecond)
  exact cross_trans _ _ _ _ _ _ movedFirst proper

theorem replace_middle (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    crossEquivalent tripleF tripleF (geometricData z R B p q A) (splitData z R B p q A) := by
  have old := GaussianGammaCompactCutoffAlignment.original_middle_alignment z R B p q A (.andI h.andE₁ h.andE₂.andE₂)
  have inner := GaussianNameArithmetic.add_equivalent nameF nameF nameF nameF
    (middleData z R B p q A) (GaussianGammaEulerCompactQuadrature.data z R B p A) (upperData z R B p q A) (upperData z R B p q A)
    (middle_regular z R B p q A h) (original_regular z R B p q A h) (upper_regular z R B p q A h) (upper_regular z R B p q A h)
    (cross_to_diagonal _ _ _ _ (cross_symm _ _ _ _ old)) (GaussianNameEquivalence.diagonal_refl _ _)
  exact GaussianNameArithmetic.add_equivalent nameF nameF (addF nameF nameF) (addF nameF nameF)
    (lowerData z R B p q A) (lowerData z R B p q A)
    (addData (middleData z R B p q A) (upperData z R B p q A))
    (addData (GaussianGammaEulerCompactQuadrature.data z R B p A) (upperData z R B p q A))
    (lower_regular z R B p q A h) (lower_regular z R B p q A h)
    (GaussianNameArithmetic.add_fast _ _ _ _ (middle_regular z R B p q A h) (upper_regular z R B p q A h))
    (GaussianNameArithmetic.add_fast _ _ _ _ (original_regular z R B p q A h) (upper_regular z R B p q A h))
    (GaussianNameEquivalence.diagonal_refl _ _) (cross_to_diagonal _ _ _ _ inner)

theorem strict_original_split (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) (hpq : Γ ⊢[PRAAx] lt p q) : Γ ⊢[PRAAx]
    crossEquivalent nameF tripleF (GaussianGammaEulerCompactQuadrature.data z R B q A) (splitData z R B p q A) :=
  cross_trans _ _ _ _ _ _ (strict_geometric_split z R B p q A h hpq) (replace_middle z R B p q A h)

theorem same_original_split (z R B p A : PTm n) (h : Γ ⊢[PRAAx] source z R B p p A) : Γ ⊢[PRAAx]
    crossEquivalent nameF tripleF (GaussianGammaEulerCompactQuadrature.data z R B p A) (splitData z R B p p A) := by
  let E := etaDen p A R
  let T := top p A R
  let L := GaussianGammaEulerCompactQuadrature.localFactor p A R
  let X := GaussianEulerIntegrandName.fixedData z B
  let old := GaussianGammaEulerCompactQuadrature.data z R B p A
  have oc := original_regular z R B p p A h
  have lc := lower_regular z R B p p A h
  have uc := upper_regular z R B p p A h
  have lowSource := piece_source z R B p p A one zero h (le_refl one)
    (le_congr (add_zero one).eqSymm (.eqRefl _) (GaussianRationalHorner.positive_product _ _
      (GaussianGammaIntegralCutoffs.eta_den_positive p A R) (GaussianGammaIntegralCutoffs.top_positive p A R)))
  have upperSource := piece_source z R B p p A (E*T) zero h
    (GaussianRationalHorner.positive_product _ _ (GaussianGammaIntegralCutoffs.eta_den_positive p A R) (GaussianGammaIntegralCutoffs.top_positive p A R))
    (le_congr (add_zero (E*T)).eqSymm (.eqRefl _) (le_refl (E*T)))
  have lowRaw := GaussianCompactZeroWidth.name_zero GaussianEulerIntegrandName.evaluatorF one E L T X old
    (GaussianEulerCompactAdditivity.compact_input _ _ _ _ _ _ _ lowSource)
  have upperRaw := GaussianCompactZeroWidth.name_zero GaussianEulerIntegrandName.evaluatorF (E*T) E L T X old
    (GaussianEulerCompactAdditivity.compact_input _ _ _ _ _ _ _ upperSource)
  have lowEq : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.data z R B one zero E T ≐ lowerData z R B p p A :=
    euler_data_congr _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _) (GaussianGammaCompactCutoffGeometry.same_lower p A).eqSymm (.eqRefl _) (.eqRefl _)
  have upperEq : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.data z R B (E*T) zero E T ≐ upperData z R B p p A :=
    euler_data_congr _ _ _ _ _ _ _ _ _ _ _ (.eqRefl _) (GaussianGammaCompactCutoffGeometry.same_upper p A R).eqSymm (.eqRefl _) (.eqRefl _)
  have lowZero := cross_data_congr _ _ _ _ _ _ lowEq (.eqRefl old) lowRaw
  have upperZero := cross_data_congr _ _ _ _ _ _ upperEq (.eqRefl old) upperRaw
  have innerProper := GaussianNameArithmetic.add_equivalent nameF nameF nameF GaussianNameRingLaws.zeroF old old
    (upperData z R B p p A) old oc oc uc (GaussianNameRingLaws.zero_fast old)
    (GaussianNameEquivalence.diagonal_refl _ _) (cross_to_diagonal _ _ _ _ upperZero)
  have innerZero := cross_trans _ _ _ _ _ _ innerProper (GaussianNameRingLaws.add_zero nameF old oc)
  have outerProper := GaussianNameArithmetic.add_equivalent nameF GaussianNameRingLaws.zeroF (addF nameF nameF) nameF
    (lowerData z R B p p A) old (addData old (upperData z R B p p A)) old lc (GaussianNameRingLaws.zero_fast old)
    (GaussianNameArithmetic.add_fast _ _ _ _ oc uc) oc (cross_to_diagonal _ _ _ _ lowZero) (cross_to_diagonal _ _ _ _ innerZero)
  exact cross_symm _ _ _ _ (cross_trans _ _ _ _ _ _ outerProper (GaussianNameRingLaws.add_zero_left nameF old oc))

/-- The actual later compact cutoff equals the normalized sum of its
lower piece, the UNCHANGED original earlier compact name, and upper
piece. Includes p=q with the genuine two zero-width original pieces. -/
theorem original_three_piece_split (z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    crossEquivalent nameF tripleF (GaussianGammaEulerCompactQuadrature.data z R B q A) (splitData z R B p q A) := by
  refine .orE (lt_or_eq_of_le h.andE₂.andE₂) (strict_original_split z R B p q A h.wk Prf.hyp0) ?_
  have original : (p ≐ q) :: Γ ⊢[PRAAx] crossEquivalent nameF tripleF
      (GaussianGammaEulerCompactQuadrature.data z R B p A) (splitData z R B p p A) :=
    same_original_split z R B p A (.andI h.andE₁.wk (.andI h.andE₂.andE₁.wk (le_refl p)))
  simpa using Prf.eqSubst (crossEquivalent nameF tripleF
    (GaussianGammaEulerCompactQuadrature.data (var 0) (var 1) (var 2) (var 4) (var 5))
    (splitData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) : Fm PTm 6)
    ![z,R,B,p,p,A] ![z,R,B,p,q,A] (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact .eqRefl _
      · exact .eqRefl _
      · exact .eqRefl _
      · exact Prf.hyp0
      · exact .eqRefl _) (by simpa using original)

def rawSum (t z R B p q A : PTm n) : PTm n := GaussianRationalHorner.qadd (ap2 nameF t (lowerData z R B p q A))
  (GaussianRationalHorner.qadd (ap2 nameF t (GaussianGammaEulerCompactQuadrature.data z R B p A)) (ap2 nameF t (upperData z R B p q A)))
ipra_subst rawSum

theorem normalized_to_raw (t z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 tripleF t (splitData z R B p q A)) (rawSum t z R B p q A) (num 6) (GaussianCoefficientNameBounds.unit t) := by
  have lc := lower_regular z R B p q A h
  have oc := original_regular z R B p q A h
  have uc := upper_regular z R B p q A h
  have inner := GaussianNameRingLaws.add_sample_error nameF nameF (GaussianGammaEulerCompactQuadrature.data z R B p A) (upperData z R B p q A) t oc uc
  have outer := GaussianNameRingLaws.add_sample_error nameF (addF nameF nameF) (lowerData z R B p q A)
    (addData (GaussianGammaEulerCompactQuadrature.data z R B p A) (upperData z R B p q A)) t lc (GaussianNameArithmetic.add_fast _ _ _ _ oc uc)
  have held := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ) (ap2 nameF t (lowerData z R B p q A))
    (GaussianCoefficientNameBounds.unit t) (GaussianCoefficientNameBounds.unit_positive t)
  have lifted := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ (GaussianCoefficientNameBounds.unit_positive t) held inner
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ (GaussianCoefficientNameBounds.unit_positive t) outer lifted)

/-- Original requested observations compare directly with the actual
three scalar summands, keeping the real normalized addition errors. -/
theorem raw_observations (s t z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (ap2 nameF s (GaussianGammaEulerCompactQuadrature.data z R B q A)) (rawSum t z R B p q A)
      (GaussianCoefficientNameBounds.unit t+num 7*GaussianCoefficientNameBounds.unit s)
      (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) := by
  have us := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) s
  have ut := GaussianCoefficientNameBounds.unit_positive (Γ := Γ) t
  have den := GaussianRationalHorner.positive_product (Γ := Γ) _ _ us ut
  have named := GaussianNameEquivalence.cross_at nameF tripleF _ _ s t (original_three_piece_split z R B p q A h)
  have raw := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (num 6*GaussianCoefficientNameBounds.unit s)
    (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) ut den
    (le_of_eq_add (d := zero) (by ipra_ring)) (normalized_to_raw t z R B p q A h)
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ den named raw)

def output (s t z R B p q A : PTm n) : PTm n := pairT (ap2 nameF s (GaussianGammaEulerCompactQuadrature.data z R B q A))
  (pairT (rawSum t z R B p q A) (pairT (GaussianCoefficientNameBounds.unit t+num 7*GaussianCoefficientNameBounds.unit s)
    (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t)))
def outputF : PR 8 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
def run (s t z R B p q A : PTm n) : PTm n := PTm.app outputF ![s,t,z,R,B,p,q,A]
ipra_subst output
theorem program_at (s t z R B p q A : PTm n) : Γ ⊢[PRAAx] run s t z R B p q A ≐ output s t z R B p q A := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) : PTm 8) ![s,t,z,R,B,p,q,A]
theorem returned_full (s t z R B p q A : PTm n) : Γ ⊢[PRAAx]
    fstT (run s t z R B p q A) ≐ ap2 nameF s (GaussianGammaEulerCompactQuadrature.data z R B q A) :=
  (program_at s t z R B p q A).fstE
theorem returned_tail (s t z R B p q A : PTm n) : Γ ⊢[PRAAx] sndT (run s t z R B p q A) ≐ pairT (rawSum t z R B p q A)
    (pairT (GaussianCoefficientNameBounds.unit t+num 7*GaussianCoefficientNameBounds.unit s) (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t)) :=
  (program_at s t z R B p q A).sndE
theorem returned_sum (s t z R B p q A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run s t z R B p q A)) ≐ rawSum t z R B p q A :=
  (returned_tail s t z R B p q A).fstE
theorem returned_budget (s t z R B p q A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run s t z R B p q A)) ≐
    pairT (GaussianCoefficientNameBounds.unit t+num 7*GaussianCoefficientNameBounds.unit s) (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) :=
  (returned_tail s t z R B p q A).sndE
theorem returned_numerator (s t z R B p q A : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run s t z R B p q A))) ≐
    GaussianCoefficientNameBounds.unit t+num 7*GaussianCoefficientNameBounds.unit s := (returned_budget s t z R B p q A).fstE
theorem returned_denominator (s t z R B p q A : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run s t z R B p q A))) ≐
    GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t := (returned_budget s t z R B p q A).sndE
theorem returned_distance (s t z R B p q A : PTm n) (h : Γ ⊢[PRAAx] source z R B p q A) : Γ ⊢[PRAAx]
    GaussianRationalMetric.distanceBounded (fstT (run s t z R B p q A)) (fstT (sndT (run s t z R B p q A)))
      (fstT (sndT (sndT (run s t z R B p q A)))) (sndT (sndT (sndT (run s t z R B p q A)))) :=
  GaussianRationalDistanceOrder.distance_congr (returned_full s t z R B p q A).eqSymm (returned_sum s t z R B p q A).eqSymm
    (returned_numerator s t z R B p q A).eqSymm (returned_denominator s t z R B p q A).eqSymm (raw_observations s t z R B p q A h)

theorem original_compact_cutoff_three_piece_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶ crossEquivalent nameF tripleF
      (GaussianGammaEulerCompactQuadrature.data (var 0) (var 1) (var 2) (var 4) (var 5))
      (splitData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_three_piece_split _ _ _ _ _ _ Prf.hyp0))
theorem original_equal_cutoff_three_piece_split_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 3) (var 4) ⟶ crossEquivalent nameF tripleF
      (GaussianGammaEulerCompactQuadrature.data (var 0) (var 1) (var 2) (var 3) (var 4))
      (splitData (var 0) (var 1) (var 2) (var 3) (var 3) (var 4))) :=
  closeUniv 5 (.impI (same_original_split _ _ _ _ _ Prf.hyp0))
theorem actual_original_cutoff_piece_names_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      (pointCN nameF (lowerData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) ⋏
        (pointCN nameF (GaussianGammaEulerCompactQuadrature.data (var 0) (var 1) (var 2) (var 3) (var 5)) ⋏
          pointCN nameF (upperData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))))) :=
  closeUniv 6 (.impI (.andI (lower_regular _ _ _ _ _ _ Prf.hyp0)
    (.andI (original_regular _ _ _ _ _ _ Prf.hyp0) (upper_regular _ _ _ _ _ _ Prf.hyp0))))
theorem original_cutoff_split_raw_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianRationalMetric.distanceBounded (ap2 nameF (var 0) (GaussianGammaEulerCompactQuadrature.data (var 2) (var 3) (var 4) (var 6) (var 7)))
        (rawSum (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))
        (GaussianCoefficientNameBounds.unit (var 1)+num 7*GaussianCoefficientNameBounds.unit (var 0))
        (GaussianCoefficientNameBounds.unit (var 0)*GaussianCoefficientNameBounds.unit (var 1))) :=
  closeUniv 8 (.impI (raw_observations _ _ _ _ _ _ _ _ Prf.hyp0))
theorem actual_cutoff_split_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (program_at _ _ _ _ _ _ _ _)
theorem actual_returned_cutoff_split_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      GaussianRationalMetric.distanceBounded (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))
        (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)))))) :=
  closeUniv 8 (.impI (returned_distance _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaCompactCutoffSplit
