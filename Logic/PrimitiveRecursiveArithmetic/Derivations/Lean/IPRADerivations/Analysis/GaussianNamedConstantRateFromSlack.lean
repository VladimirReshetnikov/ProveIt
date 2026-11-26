import IPRADerivations.Analysis.GaussianNamedRateTransport
import IPRADerivations.Analysis.GaussianGammaCanonicalExponent

/-!
# A sharp constant comparison from late observations

A common estimate `A/D + C/2^t` at every observation clock of a
regular name certifies the exact radius `A/D`, with only the intrinsic
observation errors at the requested clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedConstantRateFromSlack

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSlackRemoval (slack allSlack slack_removal)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def sampleSlack (f : PR 2) (x y A D C : PTm n) : Fm PTm n :=
  .all (slack (qsub (ap2 f (var 0) (Syn.shift x)) (Syn.shift y)) (Syn.shift A) (Syn.shift D) (Syn.shift C) (var 0))

@[simp] theorem subst_sampleSlack {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x y A D C : PTm n) :
    (sampleSlack f x y A D C).subst σ = sampleSlack f (Syn.subst σ x) (Syn.subst σ y)
      (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ C) := by simp [sampleSlack,Syn.subst_shift,Syn.shift_subst]

theorem sample_slack_at (f : PR 2) (x y A D C t : PTm n) (hs : Γ ⊢[PRAAx] sampleSlack f x y A D C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f t x) y (A*unit t+C*D) (D*unit t) := by
  change Γ ⊢[PRAAx] slack (qsub (ap2 f t x) y) A D C t
  simpa only [sampleSlack,GaussianRationalSlackRemoval.subst_slack,GaussianRationalMetric.subst_qsub,
    subst_ap2,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hs.allE t

private theorem observation_slack (f : PR 2) (x y A D C p t : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] sampleSlack f x y A D C) :
    Γ ⊢[PRAAx] slack (qsub (ap2 f p x) y) (A*unit p+D) (D*unit p) (C+one) t := by
  let U := unit p
  let V := unit t
  let a := ap2 f p x
  let b := ap2 f t x
  let W := D*U
  let Z := W*V
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) t
  have hZ := positive_product W V (positive_product _ _ hD hU) hV
  have sampleBound : Γ ⊢[PRAAx] distanceBounded b y (A*V+C*D) (D*V) := sample_slack_at f x y A D C t hs
  have fromPoint := GaussianNameEquivalence.point_at f x p t hf
  have early : Γ ⊢[PRAAx] distanceBounded a b ((U+V)*D) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hU hV) hZ
      (le_of_eq_add (d := zero) (by dsimp only [Z,W]; ipra_ring)) fromPoint
  have late : Γ ⊢[PRAAx] distanceBounded b y ((A*V+C*D)*U) Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hD hV) hZ
      (le_of_eq_add (d := zero) (by dsimp only [Z,W]; ipra_ring)) sampleBound
  have e : Γ ⊢[PRAAx] (U+V)*D+(A*V+C*D)*U ≐ (A*U+D)*V+(C+one)*W := by dsimp only [W]; ipra_ring
  exact distance_congr (.eqRefl _) (.eqRefl _) e (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hZ early late)

theorem observation_bound (f : PR 2) (x y A D C p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] sampleSlack f x y A D C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) y (A*unit p+D) (D*unit p) := by
  apply slack_removal _ _ _ (C+one) (positive_product _ _ hD (unit_positive p))
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hF' : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift
  have hD' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hD.shift
  have hS' : Δ ⊢[PRAAx] sampleSlack f (sh x) (sh y) (sh A) (sh D) (sh C) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  simpa only [allSlack,Syn.shift,sh,GaussianRationalMetric.subst_qsub,subst_ap2,
    PTm.subst_add,PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observation_slack f (sh x) (sh y) (sh A) (sh D) (sh C) (sh p) (var 0) hF' hD' hS'

theorem observation_rate (f : PR 2) (x y A D C p q : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] sampleSlack f x y A D C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 constantF q y) (rateNumerator A D p q) (rateDenominator D p q) := by
  let U := unit p
  have hW := positive_product D U hD (unit_positive p)
  have hZ := denominator_positive D p q hD
  have fit : Γ ⊢[PRAAx] le ((A*U+D)*rateDenominator D p q) (rateNumerator A D p q*(D*U)) :=
    le_of_eq_add (d := D*U*(D*U)) (by dsimp only [U,rateNumerator,rateDenominator]; ipra_ring)
  exact distance_congr (.eqRefl _) (constant_at q y).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ hW hZ fit (observation_bound f x y A D C p hf hD hs))

theorem independent_rate (f : PR 2) (x y A D C : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hD : Γ ⊢[PRAAx] le one D)
    (hs : Γ ⊢[PRAAx] sampleSlack f x y A D C) :
    Γ ⊢[PRAAx] independentRate f constantF x y A D := by
  refine .allI (.allI ?_)
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hF' : Δ ⊢[PRAAx] pointCN f (sh x) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hf.shift.shift
  have hD' : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hD.shift.shift
  have hS' : Δ ⊢[PRAAx] sampleSlack f (sh x) (sh y) (sh A) (sh D) (sh C) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.shift
  exact observation_rate f (sh x) (sh y) (sh A) (sh D) (sh C) (var 1) (var 0) hF' hD' hS'

end LeanProofs.IPRA.Analysis.GaussianNamedConstantRateFromSlack
