import IPRADerivations.Analysis.GaussianGammaHalfWallisRate

/-!
# A regular name from the original arctangent quadrature

The Gamma packet defines π as four times the integral of (1/(1+t^2))
on the unit interval. Each observation below is four times the existing
rational left grid for that integrand. The finite Wallis comparison
provides a common rational anchor for independent mesh precisions and a
uniform bound on all later grids.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaHalfPiName

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaHalfWallisRate (wallisValue piGrid arctanError arctanDen gridSource finite_rate)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open WallisFinite (Dm)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def orderIndex (p : PTm n) : PTm n := num 16*unit p
def orderAt (p : PTm n) : PTm n := succ (orderIndex p)
def meshIndex (p : PTm n) : PTm n := num 8*Dm (orderAt p)*unit p
def meshAt (p : PTm n) : PTm n := succ (meshIndex p)
def clearing (p : PTm n) : PTm n := two*(meshAt p*meshAt p)
def observation (p : PTm n) : PTm n := piGrid (meshAt p) (clearing p)
def nameF : PR 2 := PTm.toPR (observation (var 0) : PTm 2)

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

private theorem succ_le_succ {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (succ a) (succ b) := by ipra_le sl h

theorem unit_mono (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (unit p) (unit q) :=
  GaussianFactorBudget.power_monotone_length two p q (zero_lt_succ one) h

theorem order_mono (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (orderAt p) (orderAt q) := by
  have b := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 16)) (unit_mono p q h)
  exact succ_le_succ b

theorem Dm_mono (N K : PTm n) (h : Γ ⊢[PRAAx] le N K) : Γ ⊢[PRAAx] le (Dm N) (Dm K) := by
  have hb := GaussianFactorBudget.power_monotone_length two N K (zero_lt_succ one) h
  have hm := AnalyticNumberTheory.PhiLower.le_mul_mono (succ_le_succ h) (succ_le_succ h)
  exact AnalyticNumberTheory.PhiLower.le_mul_mono (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 16)) hb) hm

theorem mesh_mono (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) : Γ ⊢[PRAAx] le (meshAt p) (meshAt q) := by
  have d := Dm_mono _ _ (order_mono p q h)
  exact succ_le_succ (AnalyticNumberTheory.PhiLower.le_mul_mono
    (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl (num 8)) d) (unit_mono p q h))

theorem rate_budget (p m : PTm n) (hm : Γ ⊢[PRAAx] le (meshAt p) (succ m)) :
    Γ ⊢[PRAAx] le (arctanError (orderAt p) (succ m)*(two*unit p)) (arctanDen (orderAt p) (succ m)) := by
  let U := unit p
  let D := Dm (orderAt p)
  let M := succ m
  let N := orderAt p
  have hN : Γ ⊢[PRAAx] le (num 16*U) N := le_succ_self _
  have hM : Γ ⊢[PRAAx] le (num 8*D*U) M := le_trans (le_succ_self _) hm
  have twice : Γ ⊢[PRAAx]
      le (two*(arctanError N M*(two*U))) (two*arctanDen N M) := by
    change Γ ⊢[PRAAx] le (two*((num 4*M+two*N*D)*(two*U))) (two*(N*M))
    ipra_le 𝔞 M * sl hN + 𝔞 N * sl hM
  exact mul_le_cancel (d' := one) twice

theorem large_mesh_error (p m L : PTm n) (hm : Γ ⊢[PRAAx] le (meshAt p) (succ m))
    (hL : Γ ⊢[PRAAx] gridSource m L) :
    Γ ⊢[PRAAx] distanceBounded (wallisValue (orderAt p)) (piGrid (succ m) L) one (two*unit p) := by
  apply distance_radius_mono _ _ _ _ _ _
    (GaussianGammaHalfWallisRate.arctan_denominator_positive (orderIndex p) m)
    (positive_product _ _ (zero_lt_succ one) (unit_positive p)) ?_ (finite_rate (orderIndex p) m L hL)
  exact le_congr (.eqRefl _) (by unfold orderAt; ipra_ring) (rate_budget p m hm)

theorem ordered_grid_error (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (wallisValue (orderAt p)) (observation q) one (two*unit p) :=
  large_mesh_error p (meshIndex q) (clearing q) (mesh_mono p q h) (le_refl _)

theorem ordered_grid_coherence (p q : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (observation p) (observation q) (unit p+unit q) (unit p*unit q) := by
  let D := two*unit p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (zero_lt_succ one) (unit_positive p)
  have first := ordered_grid_error (Γ := Γ) p p (le_refl p)
  have second := ordered_grid_error p q h
  have joined := distance_triangle_same _ _ _ one one D hD (distance_symmetric _ _ _ _ hD first) second
  have cmp : Γ ⊢[PRAAx] le ((one+one)*(unit p*unit q)) ((unit p+unit q)*D) := by
    dsimp only [D]
    ipra_le 2 * 𝔞 (unit p) * 𝔞 (unit p)
  exact distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive p) (unit_positive q)) cmp joined

theorem grid_coherence (p q : PTm n) :
    Γ ⊢[PRAAx] distanceBounded (observation p) (observation q) (unit p+unit q) (unit p*unit q) := by
  refine .orE (le_total p q) ?_ ?_
  · exact ordered_grid_coherence p q Prf.hyp0
  · have hp := positive_product (Γ := (le q p)::Γ) _ _ (unit_positive q) (unit_positive p)
    exact distance_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (distance_symmetric _ _ _ _ hp (ordered_grid_coherence q p Prf.hyp0))

private theorem observation_subst {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) :
    Syn.subst σ (observation p) = observation (Syn.subst σ p) := by
  simp [observation,piGrid,clearing,meshAt,meshIndex,orderAt,orderIndex,WallisFinite.Dm,Products.fact]

theorem sample_at (p x : PTm n) : Γ ⊢[PRAAx] ap2 nameF p x ≐ observation p := by
  simpa only [nameF,ap2,observation_subst,Syn.subst_var,Matrix.cons_val_zero] using
    (toPR_eq (Γ := Γ) (observation (var 0) : PTm 2) ![p,x])

theorem name_regular (x : PTm n) : Γ ⊢[PRAAx] pointCN nameF x :=
  .allI (.allI (distance_congr (sample_at _ _).eqSymm (sample_at _ _).eqSymm (.eqRefl _) (.eqRefl _)
    (grid_coherence _ _)))

theorem actual_Pi_arctangent_name_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 (pointCN nameF (var 0)) :=
  closeUniv 1 (name_regular _)

theorem actual_Pi_arctangent_late_grid_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le (meshAt (var 0)) (succ (var 1)) ⟶ gridSource (var 1) (var 2) ⟶
        distanceBounded (wallisValue (orderAt (var 0))) (piGrid (succ (var 1)) (var 2)) one (two*unit (var 0))) :=
  closeUniv 3 (.impI (.impI (large_mesh_error _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaHalfPiName
