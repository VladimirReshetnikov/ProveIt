import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponentialStages

/-!
# Actual bounded integer scaling of the original exponential

The original stage successor and its derived fixed bounds feed a genuine
guarded QF numerical error induction at one requested precision. Finite
envelope removal identifies the actual exponential of E times the input
name with the actual Gaussian-rational power of its original base value.
No induction over names or equivalence formulas is used.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedIntegerExponential

open_ipra
open GaussianBoundedIntegerExponentialStages
  (input scaledF stageData radius expF expData point majorant powerBudget point_regular point_zero
    point_bound one_error power_bound successor_product_error)
open GaussianRationalReciprocal (power)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def stepCost (E R A : PTm n) : PTm n := two+num 4*majorant E R+two*powerBudget E A
def multiplier (E R A : PTm n) : PTm n := majorant E R+stepCost E R A+one
def error (E i R A : PTm n) : PTm n := pw (multiplier E R A) (succ i)
ipra_subst stepCost
ipra_subst multiplier
ipra_subst error

theorem multiplier_positive (E R A : PTm n) : Γ ⊢[PRAAx] le one (multiplier E R A) :=
  le_congr (.eqRefl _) (by unfold multiplier; ipra_ring) (le_add_right one (majorant E R+stepCost E R A))
theorem error_positive (E i R A : PTm n) : Γ ⊢[PRAAx] le one (error E i R A) :=
  GaussianFactorBudget.power_positive _ _ (multiplier_positive E R A)
theorem error_growth (E i R A : PTm n) : Γ ⊢[PRAAx]
    le (majorant E R*error E i R A+stepCost E R A) (error E (succ i) R A) := by
  have positive := error_positive (Γ := Γ) E i R A
  ipra_le 𝔞(stepCost E R A)*sl positive+𝔞(error E i R A) using
    unfold error
    rw [natEq (pw_succ (Γ := Γ) (multiplier E R A) (succ i))]
    unfold multiplier
    ipra_simps
    ring

theorem error_zero (f : PR 2) (p E R x c A : PTm n) : Γ ⊢[PRAAx]
    distanceBounded (point f p E zero R x) (power c zero) (error E zero R A) (unit p) := by
  have exactZero := distance_congr (Γ := Γ) (point_zero f p E R x).eqSymm (GaussianRationalReciprocal.power_zero c).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianRationalPowerDifference.distance_refl_zero qone (unit p) (unit_positive p))
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p)
    (le_of_eq_add (d := error E zero R A*unit p) (by ipra_ring)) exactZero

theorem error_step (f : PR 2) (p E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le (succ i) E)
    (ih : Γ ⊢[PRAAx] distanceBounded (point f p E i R x) (power c i) (error E i R A) (unit p)) : Γ ⊢[PRAAx]
    distanceBounded (point f p E (succ i) R x) (power c (succ i)) (error E (succ i) R A) (unit p) := by
  have current := le_trans (le_succ_self i) hi
  have oneE := le_trans (zero_lt_succ i) hi
  have raw := GaussianNameArithmetic.product_distance (point f p E i R x) (power c i) (point f p E one R x) c
    (error E i R A) two (unit p) (majorant E R) (powerBudget E A) (unit_positive p) ih (one_error f p E R x c A h oneE)
    (point_bound f p E one R x c A h oneE) (power_bound c A E i h.andE₂.andE₂ current)
  have right := distance_congr (.eqRefl _) (GaussianRationalReciprocal.power_succ c i).eqSymm (.eqRefl _) (.eqRefl _) raw
  have chain := distance_triangle_same _ _ _ _ _ _ (unit_positive p) (successor_product_error f p E i R x c A h hi) right
  apply distance_radius_mono _ _ _ _ _ _ (unit_positive p) (unit_positive p) _ chain
  exact le_congr (by unfold stepCost; ipra_ring) (.eqRefl _)
    (AnalyticNumberTheory.PhiLower.le_mul_mono (error_growth E i R A) (le_refl (unit p)))

/-- Every bound variable is numerical and the original input clock is
fixed by E at every stage. The quantified source law is never inducted. -/
theorem prefix_error (f : PR 2) (p E i R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A)
    (hi : Γ ⊢[PRAAx] le i E) : Γ ⊢[PRAAx]
    distanceBounded (point f p E i R x) (power c i) (error E i R A) (unit p) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) (Syn.shift c) (Syn.shift A) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have hall : Γ ⊢[PRAAx] .all (le (var 0) (Syn.shift E) ⟶
      distanceBounded (point f (Syn.shift p) (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift x)) (power (Syn.shift c) (var 0))
        (error (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift A)) (unit (Syn.shift p))) := by
    ipra_qfind (⟨trivial,trivial⟩) [subst_le, GaussianRationalMetric.subst_distanceBounded,
        GaussianBoundedIntegerExponentialStages.subst_point, GaussianRationalReciprocal.subst_power, subst_error,
        GaussianCoefficientNameBounds.subst_unit]
    · exact .impI (error_zero f p E R x c A)
    · refine .impI ?_
      let IH : Fm PTm (n+1) := le (var 0) (Syn.shift E) ⟶
        distanceBounded (point f (Syn.shift p) (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift x)) (power (Syn.shift c) (var 0))
          (error (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift A)) (unit (Syn.shift p))
      let D := le (succ (var 0)) (Syn.shift E) :: IH :: Γ.map Fm.shift
      have old : D ⊢[PRAAx] distanceBounded (point f (Syn.shift p) (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift x))
          (power (Syn.shift c) (var 0)) (error (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift A)) (unit (Syn.shift p)) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self (var 0 : PTm (n+1))) Prf.hyp0)
      exact error_step f (Syn.shift p) (Syn.shift E) (var 0) (Syn.shift R) (Syn.shift x) (Syn.shift c) (Syn.shift A) hs.wk.wk Prf.hyp0 old
  have gate : Γ ⊢[PRAAx] le i E ⟶ distanceBounded (point f p E i R x) (power c i) (error E i R A) (unit p) := by
    simpa only [Fm.subst_imp,subst_le,GaussianRationalMetric.subst_distanceBounded,GaussianBoundedIntegerExponentialStages.subst_point,
      GaussianRationalReciprocal.subst_power,subst_error,GaussianCoefficientNameBounds.subst_unit,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hall.allE i
  exact .impE gate hi

theorem final_envelope (f : PR 2) (E R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A) : Γ ⊢[PRAAx]
    GaussianValueNormalizerExtensionality.rawDiagonal (expF f) constantF (expData E E R x) (power c E) (error E E R A) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] input f (Syn.shift R) (Syn.shift x) (Syn.shift c) (Syn.shift A) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  have finite := prefix_error f (var 0) (Syn.shift E) (Syn.shift E) (Syn.shift R) (Syn.shift x) (Syn.shift c) (Syn.shift A) hs (le_refl _)
  have actual := distance_congr (.eqRefl _) (GaussianGammaCanonicalExponent.constant_at (var 0) (power (Syn.shift c) (Syn.shift E))).eqSymm
    (.eqRefl _) (.eqRefl _) finite
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,point,GaussianBoundedIntegerExponentialStages.subst_expData,
    GaussianRationalReciprocal.subst_power,subst_error,Syn.shift] using actual

/-- The actual capped integer exponential is the actual normalized
rational power for every internal E, including zero and raw base values. -/
theorem integer_power_cross (f : PR 2) (E R x c A : PTm n) (h : Γ ⊢[PRAAx] input f R x c A) : Γ ⊢[PRAAx]
    crossEquivalent (expF f) constantF (expData E E R x) (power c E) :=
  GaussianNameRingLaws.equivalent_of_envelope (expF f) constantF (expData E E R x) (power c E) (error E E R A)
    (point_regular f E E R x c A h (le_refl _)) (GaussianGammaCanonicalExponent.constant_regular _) (final_envelope f E R x c A h)

theorem original_bounded_integer_exponential_prefix_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (input f (var 3) (var 4) (var 5) (var 6) ⟶ le (var 2) (var 1) ⟶
      distanceBounded (point f (var 0) (var 1) (var 2) (var 3) (var 4)) (power (var 5) (var 2))
        (error (var 1) (var 2) (var 3) (var 6)) (unit (var 0))) :=
  closeUniv 7 (.impI (.impI (prefix_error f _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_bounded_integer_exponential_power_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (input f (var 1) (var 2) (var 3) (var 4) ⟶
      crossEquivalent (expF f) constantF (expData (var 0) (var 0) (var 1) (var 2)) (power (var 3) (var 0))) :=
  closeUniv 5 (.impI (integer_power_cross f _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBoundedIntegerExponential
