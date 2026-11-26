import IPRADerivations.Analysis.Gamma.EulerProducts.Approximants.GaussianGammaFiniteApproximantName
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate
import IPRADerivations.Analysis.Polynomials.RootFinding.Reconstruction.GaussianReconstructionRoots

/-!
# Exponential comparison with a frozen named input

A dyadic independent rate bounds every observation of the frozen name
in a common disk. At the original exponential's actual query clock,
the dyadic error fits its precision budget.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRadiusExponentialFreeze

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameBounds (U)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at diagonal_rate)
open GaussianRadiusExponentialName
  (boundedSamples nameF data input index inputPrecision precision_budget query_bound sample_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRadiusExponentialLipschitz (factor scalar_sum_lipschitz)
open GaussianRationalReciprocal (bound_congr)
open GaussianReconstructionRoots (norm_from_distance)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def radius (f : PR 2) (x : PTm n) : PTm n := U f x + num 3

ipra_subst radius

theorem original_input (f : PR 2) (x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] input f (radius f x) x :=
  GaussianExponentialRadiusIndependence.input_widen f (U f x) (radius f x) x
    (GaussianGammaFiniteApproximantName.exponential_input f x h) (le_add_right _ _)

theorem partner_bound (f g : PR 2) (x y s p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (h : Γ ⊢[PRAAx] independentRate f g x y one (unit s)) :
    Γ ⊢[PRAAx] bounded (ap2 g p y) (radius f x) one := by
  let u := ap2 f zero x
  let v := ap2 g p y
  let S := unit s
  let P := unit p
  let Z : PTm n := unit zero
  have hs := unit_positive (Γ := Γ) s
  have hp := unit_positive (Γ := Γ) p
  have hz := unit_positive (Γ := Γ) (zero : PTm n)
  have den := GaussianNamedInverseRate.denominator_positive S zero p hs
  have comparison : Γ ⊢[PRAAx] distanceBounded v u (num 3) one :=
    distance_radius_mono v u _ _ (num 3) one den (le_refl one)
      (by
        dsimp only [rateNumerator, rateDenominator]
        ipra_le 𝔞(Z)*𝔞(P)*sl hs+𝔞(S)*𝔞(Z)*sl hp+𝔞(S)*𝔞(P)*sl hz)
      (distance_symmetric u v _ _ den (rate_at f g x y one S zero p h))
  exact bound_congr (.eqRefl _) (by unfold radius; ipra_ring) (by ipra_ring)
    (norm_from_distance v u (num 3) one (U f x) one (le_refl one) (le_refl one)
      comparison (GaussianNameBounds.sample_bound f x zero hf))

theorem partner_input (f g : PR 2) (x y s : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] independentRate f g x y one (unit s)) :
    Γ ⊢[PRAAx] input g (radius f x) y := by
  refine .andI hg (.allI ?_)
  let sh (z : PTm n) := Syn.shift z
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointCN f (sh x) := by
    simpa only [Fm.shift, Syn.shift, sh, GaussianEuclideanDistanceName.subst_pointCN] using hf.shift
  have hr : Γ.map Fm.shift ⊢[PRAAx] independentRate f g (sh x) (sh y) one (unit (sh s)) := by
    simpa only [Fm.shift, Syn.shift, sh, GaussianNamedInverseRate.subst_independentRate,
      GaussianCoefficientNameBounds.subst_unit, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      using h.shift
  simpa only [boundedSamples, Syn.shift, sh, subst_radius] using
    partner_bound f g (sh x) (sh y) (sh s) (var 0) hs hr

theorem exponential_distance (f g : PR 2) (W x y p : PTm n)
    (hf : Γ ⊢[PRAAx] input f W x) (hg : Γ ⊢[PRAAx] input g W y)
    (h : Γ ⊢[PRAAx] independentRate f g x y one (unit (inputPrecision W p))) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data W x)) (ap2 (nameF g) p (data W y)) one (unit p) := by
  let t := inputPrecision W p
  let K := index W p
  let u := ap2 f t x
  let v := ap2 g t y
  have ht := unit_positive (Γ := Γ) t
  have near : Γ ⊢[PRAAx] distanceBounded u v (num 3) (unit t) :=
    distance_radius_mono _ _ _ _ (num 3) (unit t) (positive_product _ _ ht ht) ht
      (le_of_eq_add (d := zero) (by ipra_ring)) (diagonal_rate f g x y one (unit t) t ht h)
  have raw := scalar_sum_lipschitz u v W (num 3) (unit t) K ht
    (query_bound f W x p hf) (query_bound g W y p hg) near
  have budget : Γ ⊢[PRAAx] le (factor W K * num 3 * unit p) (one * unit t) :=
    le_trans
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (factor W K * unit p) (le_succ_self (num 3))))
      (le_congr (.eqRefl _) (one_mul _).eqSymm (precision_budget W p))
  exact distance_congr (sample_at f W p x).eqSymm (sample_at g W p y).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ one (unit p) ht (unit_positive p) budget raw)

theorem actual_radius_exponential_frozen_observation_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (input f (var 0) (var 1) ⟶ input g (var 0) (var 2) ⟶
        independentRate f g (var 1) (var 2) one (unit (inputPrecision (var 0) (var 3))) ⟶
        distanceBounded (ap2 (nameF f) (var 3) (data (var 0) (var 1)))
          (ap2 (nameF g) (var 3) (data (var 0) (var 2))) one (unit (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (exponential_distance f g _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedRadiusExponentialFreeze
