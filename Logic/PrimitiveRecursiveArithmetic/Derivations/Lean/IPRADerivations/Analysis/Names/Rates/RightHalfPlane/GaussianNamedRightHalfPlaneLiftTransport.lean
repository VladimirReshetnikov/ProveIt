import IPRADerivations.Analysis.Names.RightHalfPlane.GaussianNamedRightHalfPlaneLift
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Transport a rational-map lift through pointwise equivalence

An equivalent evaluator inherits the same spatial gain and input
clock. Its lift still evaluates the new program on each frozen input
sample, so the equivalence applies to the actual lifted programs.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneLiftTransport

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedRightHalfPlaneLift (RationalMap source clock nameF data frozenData late_certificate clock_margin sample_at)
open GaussianNamedRightHalfPlaneSigned (certificate)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def PointAgreement (base : RationalMap) (evaluate : PR 2) (readData : PR 1) : Prop :=
  ∀ {m : ℕ} {Δ : List (Fm PTm m)} (z R K : PTm m),
    (Δ ⊢[PRAAx] certificate z R K) →
      (Δ ⊢[PRAAx] crossEquivalent base.evaluator evaluate (ap1 base.rationalData z) (ap1 readData z))

def transportedMap (base : RationalMap) (evaluate : PR 2) (readData : PR 1)
    (agree : PointAgreement base evaluate readData) : RationalMap where
  evaluator := evaluate
  rationalData := readData
  gain := base.gain
  variation := fun x y R K E D hx hy hD small near =>
    GaussianNamedRateTransport.transport base.evaluator base.evaluator evaluate evaluate
      (ap1 base.rationalData x) (ap1 base.rationalData y) (ap1 readData x) (ap1 readData y)
      (ap2 base.gain R K*E) D hD (base.variation x y R K E D hx hy hD small near)
      (cross_symm _ _ _ _ (agree x R K hx)) (cross_symm _ _ _ _ (agree y R K hy))

private theorem successor_unit (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

theorem observation (base : RationalMap) (evaluate : PR 2) (readData : PR 1)
    (agree : PointAgreement base evaluate readData) (f : PR 2) (p x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF base f) p (data x M R))
      (ap2 (nameF (transportedMap base evaluate readData agree) f) p (data x M R)) one (unit p) := by
  let target := transportedMap base evaluate readData agree
  let k := clock base p M R
  let z := ap2 f k x
  let U := unit (succ p)
  have cert := late_certificate f x k M R h (clock_margin base p M R)
  have close := cross_at base.evaluator evaluate (ap1 base.rationalData z) (ap1 readData z)
    (succ p) (succ p) (agree z R (two*M) cert)
  have left := sample_at (Γ := Γ) base f p x M R
  have right := sample_at (Γ := Γ) target f p x M R
  have hU := unit_positive (Γ := Γ) (succ p)
  have pad : Γ ⊢[PRAAx] le ((U+U)*unit p) (one*(U*U)) := by
    refine le_of_eq_add (d := zero) ?_
    have step := natEq (successor_unit (Γ := Γ) p)
    apply deriveNat
    dsimp only [U]
    ipra_simps
    rw [step]
    ring
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ one (unit p) (positive_product _ _ hU hU) (unit_positive p) pad close)

theorem equivalent (base : RationalMap) (evaluate : PR 2) (readData : PR 1)
    (agree : PointAgreement base evaluate readData) (f : PR 2) (x M R : PTm n)
    (h : Γ ⊢[PRAAx] source f x M R) :
    Γ ⊢[PRAAx] crossEquivalent (nameF base f) (nameF (transportedMap base evaluate readData agree) f)
      (data x M R) (data x M R) := by
  let target := transportedMap base evaluate readData agree
  refine GaussianNameRingLaws.equivalent_of_envelope _ _ _ _ one
    (GaussianNamedRightHalfPlaneLift.name_regular base f x M R h)
    (GaussianNamedRightHalfPlaneLift.name_regular target f x M R h) (.allI ?_)
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (s x) (s M) (s R) := by
    simpa only [Fm.shift,Syn.shift,s,GaussianNamedRightHalfPlaneLift.subst_source] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, s,
    GaussianNamedRightHalfPlaneLift.subst_data, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    observation base evaluate readData agree f (var 0) (s x) (s M) (s R) hs

end LeanProofs.IPRA.Analysis.GaussianNamedRightHalfPlaneLiftTransport
