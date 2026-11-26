import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteFixedCutoff
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactAlignment
import IPRADerivations.Analysis.Names.GaussianNameRingLaws

/-!
# An original positive compact interval between two upper incomplete names

All three names keep their unchanged original programs. A common later
cutoff gives genuine compact additivity and exact denominator rescaling;
the original finite gap removes only that auxiliary cutoff and query.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaIntegralCutoffs (height etaDen top)
open GaussianEulerIncompleteName (upperF)
open GaussianEulerCompactAdditivity (nameF intervalSource)
open GaussianEulerIncompleteCutoff (splitPoint upperWidth denominator)
open GaussianNameArithmetic (addF addData)
open GaussianRationalHorner (qadd)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNamedInverseRate (rate_at rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {ℓ : ℕ} {Γ : List (Fm PTm ℓ)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def source (z R B A a C E T : PTm ℓ) : Fm PTm ℓ :=
  GaussianEulerIntegralGammaIdentification.source z R B A ⋏
    (le one a ⋏ (le one C ⋏ (le one E ⋏ le (a+C) (E*T))))
def leftData (z R B A a E : PTm ℓ) : PTm ℓ := GaussianEulerIncompleteName.data z R B A a E
def rightData (z R B A a C E : PTm ℓ) : PTm ℓ := GaussianEulerIncompleteName.data z R B A (a+C) E
def intervalData (z R B a C E T : PTm ℓ) : PTm ℓ := GaussianEulerCompactAdditivity.data z R B a C E T
def sumData (z R B A a C E T : PTm ℓ) : PTm ℓ := addData (intervalData z R B a C E T) (rightData z R B A a C E)
def cutoff (t a C E T : PTm ℓ) : PTm ℓ := T+GaussianEulerIncompleteCutoff.clock t a E+GaussianEulerIncompleteCutoff.clock t (a+C) E

def middleData (m z R B A a C E : PTm ℓ) : PTm ℓ :=
  GaussianEulerCompactAdditivity.data z R B (a*etaDen m A R) (C*etaDen m A R) (E*etaDen m A R) (top m A R)

@[simp] theorem subst_source {u : ℕ} (σ : Fin ℓ → PTm u) (z R B A a C E T : PTm ℓ) :
    (source z R B A a C E T).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A)
      (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [source]
@[simp] theorem subst_leftData {u : ℕ} (σ : Fin ℓ → PTm u) (z R B A a E : PTm ℓ) :
    Syn.subst σ (leftData z R B A a E) = leftData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ E) := by simp [leftData]
@[simp] theorem subst_rightData {u : ℕ} (σ : Fin ℓ → PTm u) (z R B A a C E : PTm ℓ) :
    Syn.subst σ (rightData z R B A a C E) = rightData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) := by simp [rightData]
@[simp] theorem subst_intervalData {u : ℕ} (σ : Fin ℓ → PTm u) (z R B a C E T : PTm ℓ) :
    Syn.subst σ (intervalData z R B a C E T) = intervalData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [intervalData]
@[simp] theorem subst_sumData {u : ℕ} (σ : Fin ℓ → PTm u) (z R B A a C E T : PTm ℓ) :
    Syn.subst σ (sumData z R B A a C E T) = sumData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by simp [sumData]

theorem original_interval_source (z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    intervalSource z R B a C E T :=
  .andI (.andI h.andE₁.andE₁.andE₂.andE₁.andE₁ (.andI h.andE₂.andE₂.andE₂.andE₁ h.andE₁.andE₁.andE₂.andE₁.andE₂))
    (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂)

theorem left_source (z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCofinalRate.source z R B A a E :=
  .andI h.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₁)
theorem right_source (z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    GaussianEulerIncompleteCofinalRate.source z R B A (a+C) E :=
  .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ (le_add_right _ _)) h.andE₂.andE₂.andE₂.andE₁)

theorem cutoff_left (t a C E T : PTm ℓ) : Γ ⊢[PRAAx] le (GaussianEulerIncompleteCutoff.clock t a E) (cutoff t a C E T) :=
  le_of_eq_add (d := T+GaussianEulerIncompleteCutoff.clock t (a+C) E) (by unfold cutoff; ipra_ring)
theorem cutoff_right (t a C E T : PTm ℓ) : Γ ⊢[PRAAx] le (GaussianEulerIncompleteCutoff.clock t (a+C) E) (cutoff t a C E T) := le_add_left _ _
theorem cutoff_top (t a C E T A R : PTm ℓ) : Γ ⊢[PRAAx] le T (top (cutoff t a C E T) A R) := by
  have first : Γ ⊢[PRAAx] le T (height (cutoff t a C E T) A R) :=
    le_of_eq_add (d := GaussianEulerIncompleteCutoff.clock t a E+GaussianEulerIncompleteCutoff.clock t (a+C) E+A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 10)
      (by unfold height cutoff; ipra_ring)
  exact le_trans first (le_of_eq_add (d := height (cutoff t a C E T) A R) (by unfold top; ipra_ring))

theorem middle_alignment (t z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (intervalData z R B a C E T) (middleData (cutoff t a C E T) z R B A a C E) := by
  let m := cutoff t a C E T
  let F := etaDen m A R
  have old := original_interval_source z R B A a C E T h
  have endp : Γ ⊢[PRAAx] le (a+C) (E*top m A R) :=
    le_trans old.andE₂.andE₂ (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E (cutoff_top t a C E T A R)))
  have align := GaussianEulerCompactAlignment.aligned_names z R B a C E T (top m A R) F
    (.andI old.andE₁ (.andI old.andE₂.andE₁ (.andI (GaussianGammaIntegralCutoffs.eta_den_positive m A R) (.andI old.andE₂.andE₂ endp))))
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _)
    (GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _ (by ipra_ring) (by ipra_ring) (by ipra_ring) (.eqRefl _)) align

theorem later_additivity (t z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF (addF nameF nameF)
      (GaussianEulerIncompleteCutoffParts.upperData z R B (cutoff t a C E T) A a E)
      (addData (middleData (cutoff t a C E T) z R B A a C E)
        (GaussianEulerIncompleteCutoffParts.upperData z R B (cutoff t a C E T) A (a+C) E)) := by
  let m := cutoff t a C E T
  let F := etaDen m A R
  let x := a*F
  let V := C*F
  let U := upperWidth m A R (a+C) E
  let D := denominator m A R E
  let S := top m A R
  have hr : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A (a+C) E :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁
      (.andI (le_trans h.andE₂.andE₁ (le_add_right _ _)) h.andE₂.andE₂.andE₂.andE₁))
  have interior := GaussianEulerIncompleteCutoff.split_strict_interior t m A R (a+C) E
    hr.andE₂.andE₂.andE₁ hr.andE₂.andE₂.andE₂ hr.andE₂.andE₁ (cutoff_right t a C E T)
  have endpoint : Γ ⊢[PRAAx] x+(V+U) ≐ D*S :=
    (by dsimp only [x,V,F,splitPoint]; ipra_ring : Γ ⊢[PRAAx] x+(V+U) ≐ splitPoint m A R (a+C)+U).eqTrans
      (eq_add_of_le (le_of_lt interior.andE₂)).eqSymm
  have width : Γ ⊢[PRAAx] upperWidth m A R a E ≐ V+U :=
    (congrMonus endpoint.eqSymm (.eqRefl x)).eqTrans (add_monus' (V+U) x)
  have native := (GaussianEulerIncompleteCutoffParts.piece_sources t m z R B A (a+C) E hr (cutoff_right t a C E T)).andE₂
  have hs : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B x V U D S :=
    .andI (.andI native.andE₁ (.andI (positive_product _ _ h.andE₂.andE₁ (GaussianGammaIntegralCutoffs.eta_den_positive m A R))
      (le_congr endpoint.eqSymm (.eqRefl _) (le_refl _))))
      (.andI (positive_product _ _ h.andE₂.andE₂.andE₁ (GaussianGammaIntegralCutoffs.eta_den_positive m A R))
        (GaussianGammaCompactCutoffGeometry.gap_positive _ _ interior.andE₂))
  have exactFull : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.data z R B x (V+U) D S ≐
      GaussianEulerIncompleteCutoffParts.upperData z R B m A a E :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _ (.eqRefl _) width.eqSymm (.eqRefl _) (.eqRefl _)
  have exactRight : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.data z R B (x+V) U D S ≐
      GaussianEulerIncompleteCutoffParts.upperData z R B m A (a+C) E :=
    GaussianGammaCompactCutoffSplit.euler_data_congr z R B _ _ _ _ _ _ _ _
    (by dsimp only [x,V,F,splitPoint]; ipra_ring) (.eqRefl _) (.eqRefl _) (.eqRefl _)
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ exactFull
    (GaussianGammaCompactCutoffSplit.add_data_congr _ _ _ _ (.eqRefl _) exactRight)
    (GaussianEulerCompactAdditivity.name_additivity z R B x V U D S hs)

private theorem cross_diagonal (F G : PR 2) (x y t : PTm ℓ) (he : Γ ⊢[PRAAx] crossEquivalent F G x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F t x) (ap2 G t y) two (unit t) :=
  distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) (unit_positive t)
    (le_of_eq_add (d := zero) (by ipra_ring)) (cross_at _ _ _ _ t t he)

private theorem cutoff_budget (t a C E T A R : PTm ℓ) : Γ ⊢[PRAAx]
    le (GaussianEulerCutoffCauchyComparison.combined A R*unit t) (unit (height (cutoff t a C E T) A R)) := by
  have later := le_trans (GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t a E) (cutoff_left t a C E T)
  exact le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (GaussianExponentialReference.unit_monotone
    (le_add_right (Γ := Γ) t (num 4)))) (GaussianEulerIncompleteCofinalRate.cutoff_budget t _ A R later)

private theorem rate_diagonal (F G : PR 2) (x y K J t : PTm ℓ) (hJ : Γ ⊢[PRAAx] le one J)
    (budget : Γ ⊢[PRAAx] le (K*unit t) J) (hr : Γ ⊢[PRAAx] GaussianNamedInverseRate.independentRate F G x y K J) : Γ ⊢[PRAAx]
    distanceBounded (ap2 F t x) (ap2 G t y) (num 3) (unit t) :=
  distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive J t t hJ) (unit_positive t)
    (by unfold rateNumerator rateDenominator; ipra_le (𝔞(unit t)*𝔞(unit t))*sl budget)
    (rate_at _ _ _ _ _ _ t t hr)

theorem original_diagonal (t z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 upperF t (leftData z R B A a E))
      (ap2 (addF nameF upperF) t (sumData z R B A a C E T)) (num 16) (unit t) := by
  let m := cutoff t a C E T
  let X := GaussianEulerIncompleteCutoffParts.upperData z R B m A a E
  let Y := GaussianEulerIncompleteCutoffParts.upperData z R B m A (a+C) E
  let M := middleData m z R B A a C E
  let V := intervalData z R B a C E T
  let W := rightData z R B A a C E
  let Z := ap2 upperF t (leftData z R B A a E)
  let S := ap2 (addF nameF nameF) t (addData M Y)
  let Q := ap2 (addF nameF upperF) t (sumData z R B A a C E T)
  have ut := unit_positive (Γ := Γ) t
  have leftRate := (GaussianEulerIncompleteFixedCutoff.original_cutoff_rates t m z R B A a E
    (.andI (left_source z R B A a C E T h) (cutoff_left t a C E T))).andE₂
  have rightRate := (GaussianEulerIncompleteFixedCutoff.original_cutoff_rates t m z R B A (a+C) E
    (.andI (right_source z R B A a C E T h) (cutoff_right t a C E T))).andE₂
  have bud := cutoff_budget (Γ := Γ) t a C E T A R
  have jp := unit_positive (Γ := Γ) (height m A R)
  have left : Γ ⊢[PRAAx] distanceBounded Z (ap2 nameF t X) (num 3) (unit t) := rate_diagonal _ _ _ _ _ _ _ jp bud leftRate
  have right := rate_diagonal _ _ _ _ _ _ _ jp bud rightRate
  have addition : Γ ⊢[PRAAx] distanceBounded (ap2 nameF t X) S two (unit t) :=
    cross_diagonal _ _ _ _ t (later_additivity t z R B A a C E T h)
  have midCross := middle_alignment t z R B A a C E T h
  have mid : Γ ⊢[PRAAx] distanceBounded (ap2 nameF t M) (ap2 nameF t V) two (unit t) :=
    distance_symmetric _ _ _ _ ut (cross_diagonal _ _ _ _ t midCross)
  have midCN : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF M :=
    GaussianNameEquivalence.cross_trans _ _ _ _ _ _ (GaussianNameEquivalence.cross_symm _ _ _ _ midCross) midCross
  have rightCN : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN nameF Y :=
    GaussianEulerCompactAdditivity.name_regular z R B _ _ _ _
      (GaussianEulerIncompleteCutoffParts.piece_sources t m z R B A (a+C) E
        (.andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁
          (.andI (le_trans h.andE₂.andE₁ (le_add_right _ _)) h.andE₂.andE₂.andE₂.andE₁))) (cutoff_right t a C E T)).andE₂
  have oldCN := GaussianEulerCompactAdditivity.name_regular z R B a C E T (original_interval_source z R B A a C E T h)
  have upperCN := (GaussianEulerIncompleteName.original_regular_names z R B A (a+C) E (right_source z R B A a C E T h)).andE₂
  have rawLeft := GaussianNameRingLaws.add_sample_error nameF nameF M Y t midCN rightCN
  have rawMiddle := GaussianNameArithmetic.sum_distance _ _ _ _ two (num 3) (unit t) ut mid
    (distance_symmetric _ _ _ _ ut right)
  have rawRight := distance_symmetric _ _ _ _ ut (GaussianNameRingLaws.add_sample_error nameF upperF V W t oldCN upperCN)
  have joined := distance_triangle_same Z (ap2 nameF t X) Q _ _ _ ut left
    (distance_triangle_same _ S Q _ _ _ ut addition
      (distance_triangle_same _ _ Q _ _ _ ut rawLeft
        (distance_triangle_same _ _ Q _ _ _ ut rawMiddle rawRight)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) joined


theorem original_interval_decomposition (z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    crossEquivalent upperF (addF nameF upperF) (leftData z R B A a E) (sumData z R B A a C E T) := by
  have leftCN := (GaussianEulerIncompleteName.original_regular_names z R B A a E (left_source z R B A a C E T h)).andE₂
  have oldCN := GaussianEulerCompactAdditivity.name_regular z R B a C E T (original_interval_source z R B A a C E T h)
  have rightCN := (GaussianEulerIncompleteName.original_regular_names z R B A (a+C) E (right_source z R B A a C E T h)).andE₂
  have sumCN := GaussianNameArithmetic.add_fast nameF upperF (intervalData z R B a C E T) (rightData z R B A a C E) oldCN rightCN
  have envelope : Γ ⊢[PRAAx] GaussianNamedLipschitzRate.diagonalEnvelope upperF (addF nameF upperF)
      (leftData z R B A a E) (sumData z R B A a C E T) zero one (num 16) := by
    have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
        (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using h.shift
    refine .allI ?_
    have d : Γ.map Fm.shift ⊢[PRAAx] distanceBounded
        (ap2 upperF (var 0) (leftData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift E)))
        (ap2 (addF nameF upperF) (var 0) (sumData (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T)))
        (GaussianNamedLipschitzRate.diagonalNumerator zero one (num 16) (var 0))
        (GaussianNamedLipschitzRate.diagonalDenominator one (var 0)) :=
      distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNamedLipschitzRate.diagonalNumerator; ipra_ring)
        (by unfold GaussianNamedLipschitzRate.diagonalDenominator; ipra_ring)
        (original_diagonal (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hs)
    simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,subst_leftData,subst_sumData,
      ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,PTm.subst_num,Syn.shift] using d
  have rate := GaussianNamedLipschitzRate.independent_rate upperF (addF nameF upperF)
    (leftData z R B A a E) (sumData z R B A a C E T) zero one (num 16) (le_refl one) leftCN sumCN envelope
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] GaussianNamedInverseRate.independentRate upperF (addF nameF upperF)
      (Syn.shift (Syn.shift (leftData z R B A a E))) (Syn.shift (Syn.shift (sumData z R B A a C E T))) zero one := by
    simpa only [Fm.shift,GaussianNamedInverseRate.subst_independentRate,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,Syn.shift] using rate.shift.shift
  refine .allI (.allI ?_)
  have d : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] distanceBounded
      (ap2 upperF (var 1) (Syn.shift (Syn.shift (leftData z R B A a E))))
      (ap2 (addF nameF upperF) (var 0) (Syn.shift (Syn.shift (sumData z R B A a C E T))))
      (unit (var 1)+unit (var 0)) (unit (var 1)*unit (var 0)) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold rateNumerator; ipra_ring) (by unfold rateDenominator; ipra_ring)
      (rate_at _ _ _ _ _ _ (var 1) (var 0) rs)
  exact d

theorem original_observations (p q z R B A a C E T : PTm ℓ) (h : Γ ⊢[PRAAx] source z R B A a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 upperF p (leftData z R B A a E))
      (ap2 (addF nameF upperF) q (sumData z R B A a C E T)) (unit p+unit q) (unit p*unit q) :=
  cross_at _ _ _ _ p q (original_interval_decomposition z R B A a C E T h)

theorem actual_original_upper_incomplete_interval_decomposition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      crossEquivalent upperF (addF nameF upperF) (leftData (var 0) (var 1) (var 2) (var 3) (var 4) (var 6))
        (sumData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))) :=
  closeUniv 8 (.impI (original_interval_decomposition _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteInterval
