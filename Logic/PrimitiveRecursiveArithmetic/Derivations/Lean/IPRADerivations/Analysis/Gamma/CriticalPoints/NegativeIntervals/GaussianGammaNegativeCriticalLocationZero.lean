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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
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
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def inner (p N : PTm n) : PTm n := exponent (two*residualCost N) p
def argument (p N : PTm n) : PTm n := nameData (lower (inner p N) N) (denominator (inner p N) N) N
def value (p N : PTm n) : PTm n := ap2 nameF (succ p) (argument p N)
def valueF : PR 2 := PTm.toPR (value (var 0) (var 1))

@[simp] theorem subst_inner {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (inner p N) = inner (Syn.subst σ p) (Syn.subst σ N) := by simp [inner]
@[simp] theorem subst_argument {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (argument p N) = argument (Syn.subst σ p) (Syn.subst σ N) := by simp [argument]
@[simp] theorem subst_value {k : ℕ} (σ : Fin n → PTm k) (p N : PTm n) :
    Syn.subst σ (value p N) = value (Syn.subst σ p) (Syn.subst σ N) := by simp [value]

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

theorem value_regular (N : PTm n) : Γ ⊢[PRAAx] pointCN valueF N := by
  refine .allI (.allI ?_)
  let w := Syn.shift (Syn.shift N)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have dp := value_bound (Γ := Δ) p w
  have dq := value_bound (Γ := Δ) q w
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ (unit_positive p) (unit_positive q)
    dp (distance_symmetric _ _ _ _ (unit_positive q) dq)
  change Δ ⊢[PRAAx] distanceBounded (ap2 valueF p w) (ap2 valueF q w) (unit p+unit q) (unit p*unit q)
  exact distance_congr (value_at p w).eqSymm (value_at q w).eqSymm (by ipra_ring) (.eqRefl _) joined

theorem zero_cross (N : PTm n) : Γ ⊢[PRAAx] crossEquivalent valueF constantF N qzero := by
  refine .allI (.allI ?_)
  let w := Syn.shift (Syn.shift N)
  let p : PTm (n+2) := var 1
  let q : PTm (n+2) := var 0
  let z : PTm (n+2) := qzero
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have dp := value_bound (Γ := Δ) p w
  have joined := distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (unit_positive p) (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le Groth.ι (Q.mk Δ (unit p))^2) dp
  simpa only [p,q,w,z,Syn.shift,GaussianRationalHorner.subst_qzero] using
    distance_congr (value_at p w).eqSymm (constant_at q z).eqSymm (.eqRefl _) (.eqRefl _) joined

theorem original_shifted_negative_gamma_critical_zero_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (pointCN locationF (var 0) ⋏ (pointCN valueF (var 0) ⋏ crossEquivalent valueF constantF (var 0) qzero)) :=
  closeUniv 1 (.andI (location_regular _) (.andI (value_regular _) (zero_cross _)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalLocationZero
