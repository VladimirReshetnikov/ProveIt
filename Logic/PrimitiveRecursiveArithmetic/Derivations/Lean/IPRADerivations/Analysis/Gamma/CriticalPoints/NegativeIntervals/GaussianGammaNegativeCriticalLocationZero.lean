import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalLocationResidual

/-!
# The shifted digamma vanishes at the negative critical location

At precision (p), evaluate the original shifted name at its selected
rational location on a sufficiently refined mesh. The argument is an
actual observation of the certified primitive recursive location name.
The evaluation differs from zero by at most (2^{-p}), giving a regular
composition and an exact cross-equivalence to zero.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationZero

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData mesh mesh_minimum)
open GaussianGammaNegativeCriticalGrid (denominator locationF)
open GaussianGammaNegativeCriticalLocation (lower denominator_positive location_regular)
open GaussianGammaNegativeCriticalLocationResidual (residualCost original_residual_at)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def inner (p N : PTm n) : PTm n := exponent (two*residualCost N) p
def argument (p N : PTm n) : PTm n := nameData (lower (inner p N) N) (denominator (inner p N) N) N
def value (p N : PTm n) : PTm n := ap2 nameF (succ p) (argument p N)
def valueF : PR 2 := PTm.toPR (value (var 0) (var 1))

ipra_subst inner
ipra_subst argument
ipra_subst value

theorem value_at (p N : PTm n) : Γ ⊢[PRAAx] ap2 valueF p N ≐ value p N := by
  simpa only [valueF,ap2,subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
    (toPR_eq (Γ := Γ) (value (var 0) (var 1) : PTm 2) ![p,N])

theorem clock_budget (p N : PTm n) : Γ ⊢[PRAAx]
    le (two*residualCost N*unit p) (denominator (inner p N) N) := by
  let t := inner p N
  have h := query_budget (Γ := Γ) (two*residualCost N) p
  have hm : Γ ⊢[PRAAx] le one (mesh N) := le_trans (by ipra_le 7) (mesh_minimum N)
  have spare : Γ ⊢[PRAAx] le (unit t) (denominator t N) := by
    unfold denominator
    ipra_le 𝔞(unit t)*sl hm
  exact le_trans h spare

theorem value_bound (p N : PTm n) : Γ ⊢[PRAAx] distanceBounded (value p N) qzero one (unit p) := by
  let t := inner p N
  let B := denominator t N
  let U := unit p
  let V := unit (succ p)
  let C := residualCost N
  have hb := denominator_positive (Γ := Γ) t N
  have hv := unit_positive (Γ := Γ) (succ p)
  have hu := unit_positive (Γ := Γ) p
  have h : Γ ⊢[PRAAx] le (two*C*U) B := clock_budget p N
  have eq : Γ ⊢[PRAAx] V ≐ U*two := pw_succ two p
  have e := natEq eq
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hb hv) hu (by
    change Γ ⊢[PRAAx] le ((C*V+B)*U) (one*(B*V))
    ipra_le 𝔞(U)*sl h using rw [e]; ring) (original_residual_at t (succ p) N)

/-- Exact dyadic error to zero yields a regular name and cross-equivalence to
the constant zero name. The sample readbacks use the original query precisions. -/
theorem regular_zero_of_sample_error (f : PR 2) (x : PTm n)
    (sample : PTm (n+2) → PTm (n+2))
    (readback : ∀ p, (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      ap2 f p (Syn.shift (Syn.shift x)) ≐ sample p)
    (error : ∀ p, (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      distanceBounded (sample p) qzero one (unit p)) :
    Γ ⊢[PRAAx] pointCN f x ⋏ crossEquivalent f constantF x qzero := by
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hp := unit_positive (Γ := Δ) p
  have hq := unit_positive (Γ := Δ) q
  have dp := error p
  have dq := error q
  apply Prf.andI
  · refine .allI (.allI ?_)
    change Δ ⊢[PRAAx] distanceBounded (ap2 f p (Syn.shift (Syn.shift x)))
      (ap2 f q (Syn.shift (Syn.shift x))) (unit p+unit q) (unit p*unit q)
    have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ hp hq
      dp (distance_symmetric _ _ _ _ hq dq)
    exact distance_congr (readback p).eqSymm (readback q).eqSymm (by ipra_ring) (.eqRefl _) joined
  · refine .allI (.allI ?_)
    have joined := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
      hp (positive_product _ _ hp hq) (by ipra_le Groth.ι (Q.mk Δ (unit p))^2) dp
    simpa only [p,q,Syn.shift,GaussianRationalHorner.subst_qzero] using
      distance_congr (readback p).eqSymm (constant_at q qzero).eqSymm (.eqRefl _) (.eqRefl _) joined

theorem value_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN valueF N :=
  (regular_zero_of_sample_error valueF N _ (fun p => value_at p _) (fun p => value_bound p _)).andE₁

theorem zero_cross (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent valueF constantF N qzero :=
  (regular_zero_of_sample_error valueF N _ (fun p => value_at p _) (fun p => value_bound p _)).andE₂

theorem original_shifted_negative_gamma_critical_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN locationF (var 0) ⋏ (pointCN valueF (var 0) ⋏ crossEquivalent valueF constantF (var 0) qzero)) :=
  closeUniv 1 (.andI (location_regular _) (.andI (value_regular _) (zero_cross _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationZero
