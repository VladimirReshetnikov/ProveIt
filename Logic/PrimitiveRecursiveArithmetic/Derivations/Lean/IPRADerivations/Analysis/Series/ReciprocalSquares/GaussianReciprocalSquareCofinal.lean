import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialReference
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder
import IPRADerivations.Analysis.Series.ReciprocalSquares.GaussianReciprocalSquareInterval

/-!
# Dyadic cofinal observations from reciprocal-square prefix bounds

A finite sum with prefix gaps bounded by `C/(N+r)` after `r` rows,
with `N ≥ 1`, has dyadic observations at length `C * 2^p`.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianReciprocalSquareCofinal

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder
  (distance_congr distance_from_later_observations distance_radius_mono distance_symmetric)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def finiteGaps (body : PTm 2) (x N C : PTm n) : Fm PTm n := .all (.all
  (distanceBounded (sum body (var 1+var 0) (Syn.shift (Syn.shift x)))
    (sum body (var 1) (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift C))
    (Syn.shift (Syn.shift N)+var 1)))

@[simp] theorem subst_finiteGaps {m : ℕ} (σ : Fin n → PTm m) (body : PTm 2) (x N C : PTm n) :
    (finiteGaps body x N C).subst σ =
      finiteGaps body (Syn.subst σ x) (Syn.subst σ N) (Syn.subst σ C) := by
  simp [finiteGaps,Syn.subst_shift,Syn.shift_subst]

private theorem finite_gap_at (body : PTm 2) (x N C r s : PTm n)
    (h : Γ ⊢[PRAAx] finiteGaps body x N C) :
    Γ ⊢[PRAAx] distanceBounded (sum body (r+s) x) (sum body r x) C (N+r) := by
  have hr : Γ ⊢[PRAAx] .all
      (distanceBounded (sum body (Syn.shift r+var 0) (Syn.shift x)) (sum body (Syn.shift r) (Syn.shift x))
        (Syn.shift C) (Syn.shift N+Syn.shift r)) := by
    simpa only [finiteGaps,Fm.subst_all,GaussianRationalMetric.subst_distanceBounded,
      GaussianRationalFiniteSum.subst_sum,PTm.subst_add,Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,
      Foundations.BoundedFormulas.subst_up_shift',Syn.inst_zero,Syn.inst_succ,Syn.subst_inst_shift,
      Syn.shift_var] using h.allE r
  simpa only [GaussianRationalMetric.subst_distanceBounded,GaussianRationalFiniteSum.subst_sum,
    PTm.subst_add,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using hr.allE s

theorem ordered_finite_gap (body : PTm 2) (x N C a b : PTm n)
    (h : Γ ⊢[PRAAx] finiteGaps body x N C) (hab : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] distanceBounded (sum body b x) (sum body a x) C (N+a) := by
  let c := monus b a
  have read : Γ ⊢[PRAAx] sum body (a+c) x ≐ sum body b x := by
    ipra_congr (sum body (var 0) (var 1) : PTm 2) with [(eq_add_of_le hab).eqSymm, .eqRefl _]
  exact distance_congr read (.eqRefl _) (.eqRefl _) (.eqRefl _) (finite_gap_at body x N C a c h)

theorem late_prefix_error (body : PTm 2) (x N C p r : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] finiteGaps body x N C)
    (hr : Γ ⊢[PRAAx] le (C*unit p) r) :
    Γ ⊢[PRAAx] distanceBounded (sum body r x) (sum body (C*unit p) x) one (unit p) := by
  let K := N+C*unit p
  have hK : Γ ⊢[PRAAx] le one K := le_trans hN (le_add_right _ _)
  have fit : Γ ⊢[PRAAx] le (C*unit p) (one*K) :=
    le_congr (.eqRefl _) (one_mul _).eqSymm (le_add_left _ _)
  exact distance_radius_mono _ _ _ _ _ _ hK (unit_positive p) fit
    (ordered_finite_gap body x N C (C*unit p) r h hr)

theorem prefix_error (body : PTm 2) (x N C p r : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] finiteGaps body x N C) :
    Γ ⊢[PRAAx] distanceBounded (sum body (C*unit p) x) (sum body r x)
      (C*unit p+(N+r)) ((N+r)*unit p) := by
  let U := unit p
  let K := N+r
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hk : Γ ⊢[PRAAx] le one K := le_trans hN (le_add_right _ _)
  have hkU := positive_product K U hk hu
  refine (le_total r (C*unit p)).orE ?_ ?_
  · let Δ := le r (C*unit p) :: Γ
    have d := ordered_finite_gap body x N C r (C*unit p) h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have fit : Δ ⊢[PRAAx] le (C*(K*U)) ((C*U+K)*K) := le_of_eq_add (d := K*K) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hk.wk hkU.wk fit d
  · let Δ := le (C*unit p) r :: Γ
    have d := late_prefix_error body x N C p r hN.wk h.wk (Prf.hyp0 : Δ ⊢[PRAAx] _)
    have fit : Δ ⊢[PRAAx] le (one*(K*U)) ((C*U+K)*U) := le_of_eq_add (d := C*U*U) (by ipra_ring)
    exact distance_radius_mono _ _ _ _ _ _ hu.wk hkU.wk fit (distance_symmetric _ _ _ _ hu.wk d)

theorem observations (body : PTm 2) (x N C p q : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] finiteGaps body x N C) :
    Γ ⊢[PRAAx] distanceBounded (sum body (C*unit p) x) (sum body (C*unit q) x)
      (unit p+unit q) (unit p*unit q) := by
  apply distance_from_later_observations _ _ p q
  · exact late_prefix_error body x N C p (C*unit q) hN.wk h.wk
      (le_mul_mono (le_refl C) (GaussianExponentialReference.unit_monotone Prf.hyp0))
  · exact late_prefix_error body x N C q (C*unit p) hN.wk h.wk
      (le_mul_mono (le_refl C) (GaussianExponentialReference.unit_monotone Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianReciprocalSquareCofinal
