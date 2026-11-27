import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.ParameterContinuity.GaussianGammaZetaDirichletOverlap
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedChart
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaNamedInput
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneDemandComparison
import IPRADerivations.Analysis.Euler.PositiveAxis.PowerCharts.Endpoints.GaussianEulerPowerChartTimeOrder
import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneConstant

/-!
# Named Dirichlet values on independently certified overlapping domains

The two input demands admit one shared late rational observation.
At that observation the chart witnesses can change by exact native
cofinal overlap. A common weaker certificate then identifies the
outputs on equivalent input names.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedDirichletOverlap

open_ipra
open ComplexLogarithmRemainder (oneCode re)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaZetaNamedChart (dirichletMap dirichletDataF dirichlet_data_at native_source)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNamedRightHalfPlane (marginPoint)
open GaussianNamedRightHalfPlaneDemandLift (clock frozenData clock_margin name_regular)
open GaussianNamedRightHalfPlaneDemandComparison (frozen_observations)
open GaussianNamedRightHalfPlaneLift (source data late_certificate)
open GaussianNamedRightHalfPlaneSigned (certificate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian_represents positive_product qzero)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Z" => GaussianGammaZetaDirichletCofinal.nameF

abbrev nameF (f : PR 2) : PR 2 := GaussianNamedRightHalfPlaneDemandLift.nameF dirichletMap f

theorem chart_overlap (q R S K J : PTm n) (ha : Γ ⊢[PRAAx] certificate q R K)
    (hb : Γ ⊢[PRAAx] certificate q S J) :
    Γ ⊢[PRAAx] crossEquivalent Z Z (ap3 dirichletDataF q R K) (ap3 dirichletDataF q S J) := by
  have left := native_source q R K ha
  have right := native_source q S J hb
  exact GaussianGammaCompactCutoffAlignment.cross_data_congr Z Z _ _ _ _
    (dirichlet_data_at q R K).eqSymm (dirichlet_data_at q S J).eqSymm
    (GaussianGammaZetaDirichletOverlap.original_overlap _ _ _ _ _ _ left right)

private theorem constant_margin_order (M N : PTm n) (hm : Γ ⊢[PRAAx] le one M) (h : Γ ⊢[PRAAx] le M N) :
    Γ ⊢[PRAAx] GaussianNamedPositiveExponentialOrder.realOrder constantF constantF (marginPoint N) (marginPoint M) := by
  have hn := le_trans hm h
  apply GaussianNamedRightHalfPlaneConstant.constant_real_order
  apply RationalArithmetic.order_of_representations _ _ (re oneCode) (re oneCode) N M
    (ofGaussian_represents oneCode N hn).andE₁ (ofGaussian_represents oneCode M hm).andE₁ hn hm
  apply zle_of_toZ (monus N M)
  have e := natEq (eq_add_of_le h)
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,GaussianRootAlgebra.re_one]
  ipra_simps
  linear_combination -e

theorem widen_source (f : PR 2) (x M N R S : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) (hm : Γ ⊢[PRAAx] le M N) (hr : Γ ⊢[PRAAx] le R S) :
    Γ ⊢[PRAAx] source f x N S := by
  have hM := h.andE₁.andE₂.andE₁
  have weaker := constant_margin_order M N hM hm
  have c := GaussianEulerPowerChartTimeOrder.order_trans constantF constantF f
    (marginPoint N) (marginPoint M) x weaker h.andE₁.andE₂.andE₂
  exact .andI (.andI h.andE₁.andE₁ (.andI (le_trans hM hm) c)) (le_trans h.andE₂ hr)

private theorem frozen_envelope (F H : PR 2) (p x y : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 H p y)
      (rateNumerator one (unit p) p p) (rateDenominator (unit p) p p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 H p y) (num 3) (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive p)) (unit_positive p)
    (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring)) h

theorem overlap_observations (f : PR 2) (p x M N R S : PTm n)
    (ha : Γ ⊢[PRAAx] source f x M R) (hb : Γ ⊢[PRAAx] source f x N S) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x M R)) (ap2 (nameF f) p (data x N S))
      (num 8) (unit p) := by
  let a := clock dirichletMap p M R
  let b := clock dirichletMap p N S
  let k := a+b
  let x₁ := frozenData dirichletMap f k x M R
  let x₂ := frozenData dirichletMap f k x N S
  have hk : Γ ⊢[PRAAx] le a k := le_add_right a b
  have hl : Γ ⊢[PRAAx] le b k := le_add_left b a
  have qa := late_certificate f x k M R ha (le_trans (clock_margin dirichletMap p M R) hk)
  have qb := late_certificate f x k N S hb (le_trans (clock_margin dirichletMap p N S) hl)
  have left := frozen_envelope (nameF f) Z p (data x M R) x₁
    (frozen_observations dirichletMap f p p p k x M R ha hk)
  have right := frozen_envelope (nameF f) Z p (data x N S) x₂
    (frozen_observations dirichletMap f p p p k x N S hb hl)
  have hp := unit_positive (Γ := Γ) p
  have mid := distance_radius_mono _ _ _ _ two (unit p) (positive_product _ _ hp hp) hp
    (le_of_eq_add (d := zero) (by ipra_ring))
    (cross_at Z Z x₁ x₂ p p (chart_overlap (ap2 f k x) R S (two*M) (two*N) qa qb))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp left
      (distance_triangle_same _ _ _ _ _ _ hp mid (distance_symmetric _ _ _ _ hp right)))

theorem witness_overlap (f : PR 2) (x M N R S : PTm n)
    (ha : Γ ⊢[PRAAx] source f x M R) (hb : Γ ⊢[PRAAx] source f x N S) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF f) (data x M R) (data x N S) := by
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ (num 8)
    (name_regular dirichletMap f x M R ha) (name_regular dirichletMap f x N S hb) (.allI ?_)
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] source f (sh x) (sh M) (sh R) := by simpa [Fm.shift,Syn.shift,sh,Δ] using ha.shift
  have h' : Δ ⊢[PRAAx] source f (sh x) (sh N) (sh S) := by simpa [Fm.shift,Syn.shift,sh,Δ] using hb.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,GaussianNamedRightHalfPlaneLift.subst_data,
    PTm.subst_num,Syn.shift,sh,Δ] using overlap_observations f (var 0) (sh x) (sh M) (sh N) (sh R) (sh S) h h'

theorem proper (f g : PR 2) (x y M N R S : PTm n)
    (ha : Γ ⊢[PRAAx] source f x M R) (hb : Γ ⊢[PRAAx] source g y N S)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF f) (nameF g) (data x M R) (data y N S) := by
  let P := M+N
  let Q := R+S
  have hp := widen_source f x M P R Q ha (le_add_right M N) (le_add_right R S)
  have hq := widen_source g y N P S Q hb (le_add_left N M) (le_add_left S R)
  have a := witness_overlap f x M P R Q ha hp
  have b := GaussianNamedRightHalfPlaneDemandLift.proper dirichletMap f g x y P Q hp hq he
  have c := witness_overlap g y P N Q S hq hb
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ b c)

theorem actual_original_named_Dirichlet_chart_overlap_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f (var 0) (var 2) (var 4) ⟶ source g (var 1) (var 3) (var 5) ⟶
        crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF f) (nameF g) (data (var 0) (var 2) (var 4)) (data (var 1) (var 3) (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (proper f g _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

theorem proper_at_argument (f g : PR 2) (x y M N : PTm n)
    (ha : Γ ⊢[PRAAx] GaussianGammaZetaNamedInput.source f x M)
    (hb : Γ ⊢[PRAAx] GaussianGammaZetaNamedInput.source g y N)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (GaussianGammaZetaNamedInput.minusOneF f))
      (nameF (GaussianGammaZetaNamedInput.minusOneF g))
      (data (GaussianGammaZetaNamedInput.minusOneData x) M (GaussianGammaZetaNamedInput.radius f x))
      (data (GaussianGammaZetaNamedInput.minusOneData y) N (GaussianGammaZetaNamedInput.radius g y)) := by
  let b : PTm n := qsub qzero qone
  have hr := constant_regular (Γ := Γ) b
  have same := GaussianNameArithmetic.add_equivalent f g constantF constantF x y b b
    ha.andE₁ hb.andE₁ hr hr (GaussianNameEquivalence.cross_to_diagonal _ _ _ _ he)
    (GaussianNameEquivalence.diagonal_refl _ _)
  exact proper _ _ _ _ M N _ _ (GaussianGammaZetaNamedInput.lift_source f x M ha)
    (GaussianGammaZetaNamedInput.lift_source g y N hb) same

theorem actual_original_named_Dirichlet_overlap_at_argument_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (GaussianGammaZetaNamedInput.source f (var 0) (var 2) ⟶ GaussianGammaZetaNamedInput.source g (var 1) (var 3) ⟶
        crossEquivalent f g (var 0) (var 1) ⟶
        crossEquivalent (nameF (GaussianGammaZetaNamedInput.minusOneF f)) (nameF (GaussianGammaZetaNamedInput.minusOneF g))
          (data (GaussianGammaZetaNamedInput.minusOneData (var 0)) (var 2) (GaussianGammaZetaNamedInput.radius f (var 0)))
          (data (GaussianGammaZetaNamedInput.minusOneData (var 1)) (var 3) (GaussianGammaZetaNamedInput.radius g (var 1)))) :=
  closeUniv 4 (.impI (.impI (.impI (proper_at_argument f g _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaNamedDirichletOverlap
