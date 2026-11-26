import IPRADerivations.Analysis.Euler.Logarithms.Exhaustion.GaussianNamedEulerLogarithmicFrozenRate

/-!
# Logarithmic parameter variation between two fixed certified complex names

The two input names may use independent radius and margin certificates.
Their input rate allows independent observations. We freeze both inputs
after paying its two observation errors, compare the resulting original
native integrals, and remove only the auxiliary output allowances.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicParameterRate

open_ipra
open GaussianNamedRightHalfPlane (threshold radius numerator denominator actual_late_source)
open GaussianNamedEulerLogarithmicImproper (nameF data)
open GaussianNamedEulerLogarithmicFrozenRate (frozenData frozen_rate)
open GaussianEulerLogarithmicContinuity (modulus modulus_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianExponentialReference (unit_monotone)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalSlackRemoval (slack precision slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "namedSource" => GaussianNamedRightHalfPlane.source
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def inputRadius (f : PR 2) (s j x A : PTm n) : PTm n := modulus s j (radius f x) (two*A)
def source (f g : PR 2) (s j x y A B : PTm n) : Fm PTm n :=
  namedSource f x A ⋏ (namedSource g y B ⋏ independentRate g f y x one (two*inputRadius f s j x A))
def freezeClock (f : PR 2) (t j x A m : PTm n) : PTm n :=
  threshold A+succ (modulus t j (radius f x) (two*A))+succ (succ m)

ipra_subst inputRadius
ipra_subst source

private theorem freeze_margin (f : PR 2) (t j x A m : PTm n) : Γ ⊢[PRAAx] le (threshold A) (freezeClock f t j x A m) :=
  le_trans (le_add_right _ _) (le_add_right _ _)
private theorem freeze_demand (f : PR 2) (t j x A m : PTm n) : Γ ⊢[PRAAx]
    le (succ (modulus t j (radius f x) (two*A))) (freezeClock f t j x A m) :=
  le_trans (le_add_left _ _) (le_add_right _ _)
private theorem freeze_input_budget (m r k : PTm n)
    (hr : Γ ⊢[PRAAx] le (succ (succ m)) r) (hk : Γ ⊢[PRAAx] le (succ (succ m)) k) :
    Γ ⊢[PRAAx] le (two*m*(unit k+unit r)) (unit k*unit r) := by
  have amp : Γ ⊢[PRAAx] le m (unit m) := LeanProofs.IPRA.Foundations.DyadicGain.amplitude_absorb m
  have eq : Γ ⊢[PRAAx] unit (succ (succ m)) ≐ unit m*num 4 :=
    (pw_succ two (succ m)).eqTrans ((congrMul (pw_succ two m) (.eqRefl two)).eqTrans (by unfold unit; ipra_ring))
  have debt := le_congr (.eqRefl _) eq.eqSymm (mul_le_mul_right (num 4) amp)
  have first := mul_le_mul_right (unit k) (le_trans debt (unit_monotone hr))
  have second := mul_le_mul_right (unit r) (le_trans debt (unit_monotone hk))
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ first second))

theorem native_comparison (f g : PR 2) (t s j x y A B : PTm n) (hs : Γ ⊢[PRAAx] source f g s j x y A B) :
    Γ ⊢[PRAAx] independentRate I I
      (frozenData g j y B (freezeClock g t j y B (inputRadius f s j x A)))
      (frozenData f j x A (freezeClock f t j x A (inputRadius f s j x A))) (num 5) (unit s) := by
  let m := inputRadius f s j x A
  let r := freezeClock f t j x A m
  let k := freezeClock g t j y B m
  have hm : Γ ⊢[PRAAx] le one m := modulus_positive s j (radius f x) (two*A)
  have hM := positive_product _ _ (le_succ_self one) hm
  have compare := rate_at g f y x one (two*m) k r hs.andE₂.andE₂
  have near := GaussianFastValueCut.recode_distance_bound _ _ _ _ (denominator_positive (two*m) k r hM) compare
  have pays := freeze_input_budget m r k (le_add_left (Γ := Γ) _ _) (le_add_left _ _)
  have close := distance_radius_mono _ _ _ _ one m (denominator_positive (two*m) k r hM) hm
    (by dsimp only [rateNumerator,rateDenominator]
        ipra_le 𝔞 m*sl pays) near
  have left := actual_late_source f x A r hs.andE₁ (freeze_margin f t j x A m)
  have right := actual_late_source g y B k hs.andE₂.andE₁ (freeze_margin g t j y B m)
  exact GaussianEulerLogarithmicMixedParameterRate.original_mixed_parameter_rate s j
    (numerator f r x) (numerator g k y) (radius f x) (radius g y) (denominator f r x) (denominator g k y)
    (two*A) (two*B) (.andI left (.andI right close))

private theorem compare_with_slack (f g : PR 2) (t p q s j x y A B : PTm n)
    (hs : Γ ⊢[PRAAx] source f g s j x y A B) :
    Γ ⊢[PRAAx] slack (qsub (ap2 (nameF g) p (data j y B)) (ap2 (nameF f) q (data j x A)))
      (rateNumerator (num 5) (unit s) p q) (rateDenominator (unit s) p q) (num 14) t := by
  let m := inputRadius f s j x A
  let r := freezeClock f t j x A m
  let k := freezeClock g t j y B m
  let P := unit p
  let Q := unit q
  let T := unit t
  let U := unit s
  let Z := U*P*Q*T
  have hT := unit_positive (Γ := Γ) t
  have d := denominator_positive U p q (unit_positive (Γ := Γ) s)
  have z : Γ ⊢[PRAAx] le one Z := positive_product _ _ d hT
  have rr := frozen_rate g t j y B k (.andI hs.andE₂.andE₁ (.andI (freeze_margin g t j y B m) (freeze_demand g t j y B m)))
  have lf := frozen_rate f t j x A r (.andI hs.andE₁ (.andI (freeze_margin f t j x A m) (freeze_demand f t j x A m)))
  have l := rate_at (nameF g) I (data j y B) (frozenData g j y B k) (num 5) T p t rr
  have mid := rate_at I I (frozenData g j y B k) (frozenData f j x A r) (num 5) U t t
    (native_comparison f g t s j x y A B hs)
  have right := rate_at (nameF f) I (data j x A) (frozenData f j x A r) (num 5) T q t lf
  have rightDen := denominator_positive T q t hT
  have first := distance_radius_mono _ _ _ _ ((T+num 6*P)*(U*Q)) Z (denominator_positive T p t hT) z
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,Z,P,Q,T,U]; ipra_ring)) l
  have second := distance_radius_mono _ _ _ _ ((num 5*T+two*U)*(P*Q)) Z (denominator_positive U t t (unit_positive s)) z
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,Z,P,Q,T,U]; ipra_ring)) mid
  have third := distance_radius_mono _ _ _ _ ((T+num 6*Q)*(U*P)) Z rightDen z
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,Z,P,Q,T,U]; ipra_ring))
    (distance_symmetric _ _ _ _ rightDen right)
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [rateNumerator,rateDenominator,Z,P,Q,T,U,unit]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ z first (distance_triangle_same _ _ _ _ _ _ z second third))

theorem original_observations (f g : PR 2) (p q s j x y A B : PTm n) (hs : Γ ⊢[PRAAx] source f g s j x y A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF g) p (data j y B)) (ap2 (nameF f) q (data j x A))
      (rateNumerator (num 5) (unit s) p q) (rateDenominator (unit s) p q) :=
  slack_removal_at _ _ _ (num 14) (denominator_positive _ _ _ (unit_positive s))
    (compare_with_slack f g (precision (qsub (ap2 (nameF g) p (data j y B)) (ap2 (nameF f) q (data j x A)))
      (rateNumerator (num 5) (unit s) p q) (rateDenominator (unit s) p q) (num 14)) p q s j x y A B hs)

theorem original_parameter_rate (f g : PR 2) (s j x y A B : PTm n) (hs : Γ ⊢[PRAAx] source f g s j x y A B) :
    Γ ⊢[PRAAx] independentRate (nameF g) (nameF f) (data j y B) (data j x A) (num 5) (unit s) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  have h' : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f g (sh s) (sh j) (sh x) (sh y) (sh A) (sh B) := by
    simpa only [Fm.shift,Syn.shift,subst_source,sh] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa [independentRate,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh s) (sh j) (sh x) (sh y) (sh A) (sh B) h'

theorem actual_original_logarithmic_two_named_parameter_rate_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        independentRate (nameF g) (nameF f) (data (var 1) (var 3) (var 5)) (data (var 1) (var 2) (var 4))
          (num 5) (unit (var 0))) :=
  closeUniv 6 (.impI (original_parameter_rate f g _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerLogarithmicParameterRate
