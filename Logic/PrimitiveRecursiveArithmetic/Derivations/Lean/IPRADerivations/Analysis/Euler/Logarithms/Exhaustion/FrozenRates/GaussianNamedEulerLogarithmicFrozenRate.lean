import IPRADerivations.Analysis.Euler.Logarithms.Improper.GaussianNamedEulerLogarithmicImproper

/-!
# Compare a named logarithmic integral to any sufficiently late native input

The frozen input uses the actual decoder at a caller-chosen late query.
A second query, determined by the finite integer-gap estimate, compares
that frozen input to the original named quadrature. This removes the
auxiliary observation errors and keeps the two requested output errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicFrozenRate

open_ipra
open GaussianNamedRightHalfPlane (threshold radius numerator denominator actual_late_source)
open GaussianNamedEulerLogarithmicImproper (clock clock_margin clock_demand outputPrecision nameF data name_at name_regular)
open GaussianEulerLogarithmicContinuity (modulus modulus_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalSlackRemoval (slack precision slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "idata" => GaussianEulerLogarithmicImproperName.data
local notation "Input" => GaussianNamedRightHalfPlane.source
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def frozenData (f : PR 2) (j x A k : PTm n) : PTm n :=
  idata j (numerator f k x) (radius f x) (denominator f k x) (two*A)
def source (f : PR 2) (s j x A k : PTm n) : Fm PTm n :=
  Input f x A ⋏ (le (threshold A) k ⋏ le (succ (modulus s j (radius f x) (two*A))) k)

ipra_subst frozenData
ipra_subst source

theorem late_named_observation (f : PR 2) (l v s j x A k : PTm n)
    (h : Γ ⊢[PRAAx] source f s j x A k) (hl : Γ ⊢[PRAAx] le s (outputPrecision l)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) l (data j x A)) (ap2 I v (frozenData f j x A k))
      (rateNumerator (num 5) (unit s) (outputPrecision l) v) (rateDenominator (unit s) (outputPrecision l) v) := by
  let r := clock f l j x A
  let R := radius f x
  let m := modulus s j R (two*A)
  have near := GaussianNamedGamma.input_observations f x r k m h.andE₁.andE₁
    (clock_demand f l j x A s hl) h.andE₂.andE₂
  have close := distance_radius_mono _ _ one (unit m) one m (unit_positive m)
    (modulus_positive s j R (two*A))
    (le_congr (by ipra_ring) (by unfold unit; ipra_ring) (LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb m)) near
  have current := actual_late_source f x A r h.andE₁ (clock_margin f l j x A)
  have frozen := actual_late_source f x A k h.andE₁ h.andE₂.andE₁
  have rate := GaussianEulerLogarithmicMixedParameterRate.original_mixed_parameter_rate s j
    (numerator f k x) (numerator f r x) R R (denominator f k x) (denominator f r x) (two*A) (two*A)
    (.andI frozen (.andI current close))
  exact distance_congr (name_at f l j x A).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (rate_at I I _ _ (num 5) (unit s) (outputPrecision l) v rate)

private theorem compare_with_slack (f : PR 2) (t p q s j x A k : PTm n)
    (h : Γ ⊢[PRAAx] source f s j x A k) :
    Γ ⊢[PRAAx] slack (qsub (ap2 (nameF f) p (data j x A)) (ap2 I q (frozenData f j x A k)))
      (rateNumerator (num 5) (unit s) p q) (rateDenominator (unit s) p q) two t := by
  let l := t+s
  let L := unit l
  let F := unit (outputPrecision l)
  let P := unit p
  let Q := unit q
  let S := unit s
  let T := unit t
  let Z := (S*P*Q)*T
  have hSl : Γ ⊢[PRAAx] le s (outputPrecision l) := le_trans (le_add_left _ _) (le_add_right _ _)
  have tl : Γ ⊢[PRAAx] le T L := unit_monotone (le_add_right _ _)
  have tf : Γ ⊢[PRAAx] le T F := le_trans tl (unit_monotone (le_add_right _ _))
  have z : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive S p q (unit_positive s)) (unit_positive t)
  have regular := GaussianNameEquivalence.point_at (nameF f) (data j x A) p l (name_regular f j x A h.andE₁)
  have first := distance_radius_mono _ _ _ _ ((P+T)*(S*Q)) Z
    (positive_product _ _ (unit_positive p) (unit_positive l)) z
    (by dsimp only [Z,GaussianEuclideanPointDistance.unit]
        ipra_le (𝔞(unit p))^2*𝔞 S*𝔞 Q*sl tl) regular
  have late := late_named_observation f l q s j x A k h hSl
  have second := distance_radius_mono _ _ _ _ ((num 5*Q*T+S*(Q+T))*P) Z
    (denominator_positive S (outputPrecision l) q (unit_positive s)) z
    (by dsimp only [rateNumerator,rateDenominator,Z]
        ipra_le (𝔞 S)^2*𝔞 P*(𝔞 Q)^2*sl tf) late
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [rateNumerator,rateDenominator,P,Q,S,T,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ z first second)

theorem frozen_observations (f : PR 2) (p q s j x A k : PTm n)
    (h : Γ ⊢[PRAAx] source f s j x A k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data j x A)) (ap2 I q (frozenData f j x A k))
      (rateNumerator (num 5) (unit s) p q) (rateDenominator (unit s) p q) :=
  slack_removal_at _ _ _ two (denominator_positive _ _ _ (unit_positive s))
    (compare_with_slack f (precision (qsub (ap2 (nameF f) p (data j x A)) (ap2 I q (frozenData f j x A k)))
      (rateNumerator (num 5) (unit s) p q) (rateDenominator (unit s) p q) two) p q s j x A k h)

theorem frozen_rate (f : PR 2) (s j x A k : PTm n) (h : Γ ⊢[PRAAx] source f s j x A k) :
    Γ ⊢[PRAAx] independentRate (nameF f) I (data j x A) (frozenData f j x A k) (num 5) (unit s) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh s) (sh j) (sh x) (sh A) (sh k) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using h.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,Syn.shift,sh] using
    frozen_observations f (var 1) (var 0) (sh s) (sh j) (sh x) (sh A) (sh k) hs

theorem actual_original_logarithmic_frozen_rate_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
      independentRate (nameF f) I (data (var 1) (var 2) (var 3))
        (frozenData f (var 1) (var 2) (var 3) (var 4)) (num 5) (unit (var 0))) :=
  closeUniv 5 (.impI (frozen_rate f _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicFrozenRate
