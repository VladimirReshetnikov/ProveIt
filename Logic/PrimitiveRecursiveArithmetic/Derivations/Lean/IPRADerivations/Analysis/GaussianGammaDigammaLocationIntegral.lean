import IPRADerivations.Analysis.GaussianGammaDigammaLocationInput

/-!
# The logarithmic integral at the dyadic digamma location

The named evaluator is compared to the native logarithmic integral at a
late grid fraction. A uniform native residual then gives a dyadic error
bound for the original named evaluator at every observation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationIntegral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerLogarithmicContinuity (modulus)
open GaussianExponentialReference (unit_monotone)
open GaussianGammaDigammaDyadicLocation (locationF lower)
open GaussianGammaDigammaDyadicMesh (grid)
open GaussianGammaDigammaLocationInput (frozen_log_rate named_source)
open GaussianGammaDigammaNative (derivativeData)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNameRingLaws (zeroF zero_at zero_fast equivalent_of_envelope)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive rate_at)
open GaussianNamedRightHalfPlane (threshold radius)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "L" => GaussianNamedEulerLogarithmicImproper.nameF locationF
local notation "ldata" => GaussianNamedEulerLogarithmicImproper.data

/-- A uniform residual for the native integral on the selected fractions. -/
def nativeResidual (C : PTm n) : Fm PTm n := .all
  (distanceBounded (ap2 I (var 0) (derivativeData (lower (var 0)) (grid (var 0))))
    qzero (Syn.shift C) (unit (var 0)))

@[simp] theorem subst_nativeResidual {m : ℕ} (σ : Fin n → PTm m) (C : PTm n) :
    (nativeResidual C).subst σ = nativeResidual (Syn.subst σ C) := by
  simp [nativeResidual, Syn.subst_shift, Syn.shift_subst]

theorem residual_at (k C : PTm n) (h : Γ ⊢[PRAAx] nativeResidual C) : Γ ⊢[PRAAx]
    distanceBounded (ap2 I k (derivativeData (lower k) (grid k))) qzero C (unit k) := by
  simpa [nativeResidual, Syn.subst_inst_shift] using h.allE k

private def freezeClock (p x : PTm n) : PTm n :=
  p+(threshold one+succ (modulus p one (radius locationF x) (two*one)))

theorem integral_observation (p x C : PTm n) (hr : Γ ⊢[PRAAx] nativeResidual C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 L p (ldata one x one)) qzero (C+num 7) (unit p) := by
  let k := freezeClock p x
  let U := unit p
  let z := derivativeData (lower k) (grid k)
  have ht : Γ ⊢[PRAAx] le (threshold one) k :=
    le_trans (le_add_right _ _) (le_add_left _ _)
  have hd : Γ ⊢[PRAAx] le (succ (modulus p one (radius locationF x) (two*one))) k :=
    le_trans (le_add_left _ _) (le_add_left _ _)
  have hU := unit_positive (Γ := Γ) p
  have hK := unit_positive (Γ := Γ) k
  have grow : Γ ⊢[PRAAx] le U (unit k) := unit_monotone (le_add_right _ _)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 L p (ldata one x one)) (ap2 I k z) (num 7) U := by
    have d := rate_at L I (ldata one x one) z (num 5) U p k (frozen_log_rate p one k x ht hd)
    apply distance_radius_mono _ _ _ _ _ _ (denominator_positive U p k hU) hU ?_ d
    dsimp only [rateNumerator, rateDenominator, U]
    ipra_le (𝔞 (unit p))^2*sl grow
  have last : Γ ⊢[PRAAx] distanceBounded (ap2 I k z) qzero C U :=
    distance_radius_mono _ _ _ _ _ _ hK hU (by ipra_le 𝔞 C*sl grow) (residual_at k C hr)
  exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hU first last)

theorem integral_zero (x C : PTm n) (hr : Γ ⊢[PRAAx] nativeResidual C) :
    Γ ⊢[PRAAx] crossEquivalent L zeroF (ldata one x one) x := by
  apply equivalent_of_envelope _ _ _ _ (C+num 7)
    (GaussianNamedEulerLogarithmicImproper.name_regular locationF one x one (named_source x)) (zero_fast x)
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let y := Syn.shift x
  let c := Syn.shift C
  have rr : Δ ⊢[PRAAx] nativeResidual c := by
    simpa only [Fm.shift, Syn.shift, subst_nativeResidual, Δ, c] using hr.shift
  have d := distance_congr (.eqRefl _) (zero_at p y).eqSymm (.eqRefl _) (.eqRefl _)
    (integral_observation p y c rr)
  refine .allI ?_
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, p, y, c,
    GaussianNamedEulerLogarithmicImproper.subst_data, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero,
    PTm.subst_add, PTm.subst_num] using d

theorem actual_named_digamma_location_integral_composition_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (nativeResidual (var 1) ⟶ crossEquivalent L zeroF (ldata one (var 0) one) (var 0)) :=
  closeUniv 2 (.impI (integral_zero _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaLocationIntegral
