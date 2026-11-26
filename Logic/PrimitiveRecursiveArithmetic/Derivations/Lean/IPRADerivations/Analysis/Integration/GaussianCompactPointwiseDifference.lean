import IPRADerivations.Analysis.Integration.GaussianCompactClientIndependence
import IPRADerivations.Analysis.Names.GaussianNamedDifference
import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureDifference

/-!
# Shared-grid quadrature of a named pointwise difference

Use the exact weighted rational difference identity at a common grid.
Pointwise equality of the regular names gives an explicit observation
error for the original evaluators on that grid.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianCompactPointwiseDifference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactRiemannName (evaluatorName nameData inside evaluator_at grid grid_inside
  sampleBody sampleData sample_body_at quadrature)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedDifference (nameF data sample_error)
open GaussianNameEquivalence (crossEquivalent diagonal_at cross_to_diagonal)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalQuadratureDifference (differenceBody difference_body_at weighted_difference)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound leftSum)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def differenceAt (F G H : PR 3) (x y z t : PTm n) : Fm PTm n :=
  pointCN (evaluatorName F) (nameData t x) ⋏ (pointCN (evaluatorName G) (nameData t y) ⋏
    crossEquivalent (nameF (evaluatorName F) (evaluatorName G)) (evaluatorName H)
      (data (nameData t x) (nameData t y)) (nameData t z))

def pointwise (F G H : PR 3) (a C E x y z : PTm n) : Fm PTm n :=
  .all (inside (Syn.shift a) (Syn.shift C) (Syn.shift E) (var 0) ⟶
    differenceAt F G H (Syn.shift x) (Syn.shift y) (Syn.shift z) (var 0))

@[simp] theorem subst_differenceAt {m : ℕ} (σ : Fin n → PTm m) (F G H : PR 3) (x y z t : PTm n) :
    (differenceAt F G H x y z t).subst σ =
      differenceAt F G H (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) (Syn.subst σ t) := by
  simp [differenceAt]

@[simp] theorem subst_pointwise {m : ℕ} (σ : Fin n → PTm m) (F G H : PR 3) (a C E x y z : PTm n) :
    (pointwise F G H a C E x y z).subst σ =
      pointwise F G H (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E)
        (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ z) := by
  simp [pointwise, Syn.subst_shift, Syn.shift_subst, Syn.up]

theorem raw_at (F G H : PR 3) (p x y z t : PTm n)
    (h : Γ ⊢[PRAAx] differenceAt F G H x y z t) : Γ ⊢[PRAAx]
    distanceBounded (qsub (ap3 F p t x) (ap3 G p t y)) (ap3 H p t z) (num 8) (unit p) := by
  have first := sample_error (evaluatorName F) (evaluatorName G) (nameData t x) (nameData t y) p
    h.andE₁ h.andE₂.andE₁
  have second := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ h.andE₂.andE₂)
  exact distance_congr
    (GaussianRationalSyntheticDivision.qsub_congr (evaluator_at F p t x) (evaluator_at G p t y))
    (evaluator_at H p t z) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (distance_symmetric _ _ _ _ (unit_positive p) first) second)

theorem cell (F G H : PR 3) (i p N a C E x y z : PTm n)
    (h : Γ ⊢[PRAAx] pointwise F G H a C E x y z) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] distanceBounded
      (inst2 (differenceBody (sampleBody F) (sampleBody G)) i
        (pairT (sampleData p N a C E x) (sampleData p N a C E y)))
      (inst2 (sampleBody H) i (sampleData p N a C E z)) (num 8) (unit p) := by
  let t := grid i N a C E
  have rule : Γ ⊢[PRAAx] inside a C E t ⟶ differenceAt F G H x y z t := by
    simpa only [pointwise, Fm.subst_imp, GaussianCompactRiemannName.subst_inside, subst_differenceAt,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using h.allE t
  have lhs := (difference_body_at (Γ := Γ) (sampleBody F) (sampleBody G) i
    (sampleData p N a C E x) (sampleData p N a C E y)).eqTrans
    (GaussianRationalSyntheticDivision.qsub_congr (sample_body_at F i p N a C E x) (sample_body_at G i p N a C E y))
  exact distance_congr lhs.eqSymm (sample_body_at H i p N a C E z).eqSymm (.eqRefl _) (.eqRefl _)
    (raw_at F G H p x y z t (rule.impE (grid_inside i N a C E ha hE hN (le_of_lt hi))))

theorem grid_difference (F G H : PR 3) (p N a C E x y z : PTm n)
    (h : Γ ⊢[PRAAx] pointwise F G H a C E x y z) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (qsub (quadrature F p N a C E x) (quadrature G p N a C E y))
      (quadrature H p N a C E z) (C*num 8) (E*unit p) := by
  let f := differenceBody (sampleBody F) (sampleBody G)
  let g := sampleBody H
  let d := pairT (sampleData p N a C E x) (sampleData p N a C E y)
  let e := sampleData p N a C E z
  have rows : Γ ⊢[PRAAx] termsDistance f g N d e (num 8) (unit p) := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := Γ.map Fm.shift
    let i : PTm (n+1) := var 0
    have hs : Δ ⊢[PRAAx] pointwise F G H (s a) (s C) (s E) (s x) (s y) (s z) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, subst_pointwise] using h.shift
    have as : Δ ⊢[PRAAx] le one (s a) := by simpa [Δ, s, Fm.shift, Syn.shift] using ha.shift
    have es : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ, s, Fm.shift, Syn.shift] using hE.shift
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ, s, Fm.shift, Syn.shift] using hN.shift
    simpa only [termsDistance, f, g, d, e, s, Δ, i, GaussianCompactRiemannName.subst_sampleData,
      subst_pairT, GaussianCoefficientNameBounds.subst_unit, PTm.subst_num, Syn.shift] using
      cell F G H i (s p) (s N) (s a) (s C) (s E) (s x) (s y) (s z)
        hs.wk as.wk es.wk ns.wk Prf.hyp0
  have en := positive_product E N hE hN
  have up := unit_positive (Γ := Γ) p
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ en up
    (weight_bound C E N hE hN) (sum_distance f g N d e _ _ up rows)
  have sums : Γ ⊢[PRAAx] distanceBounded (leftSum f N d C E) (leftSum g N e C E)
      (C*(N*num 8)) ((E*N)*unit p) :=
    GaussianRationalReciprocal.bound_congr
      (GaussianRationalRoundedPower.multiplication_difference (weight C E N) _ _).eqSymm
      (.eqRefl _) (.eqRefl _) raw
  have exactDiff := weighted_difference (Γ := Γ) (sampleBody F) (sampleBody G) N
    (sampleData p N a C E x) (sampleData p N a C E y) C E
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ en up) (positive_product _ _ hE up)
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr exactDiff.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) sums)

theorem actual_pointwise_difference_on_shared_compact_grid_closed (F G H : PR 3) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (pointwise F G H (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      le one (var 2) ⟶ le one (var 4) ⟶ le one (var 1) ⟶
      distanceBounded (qsub (quadrature F (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (quadrature G (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)))
        (quadrature H (var 0) (var 1) (var 2) (var 3) (var 4) (var 7)) (var 3*num 8) (var 4*unit (var 0))) :=
  closeUniv 8 (.impI (.impI (.impI (.impI (grid_difference F G H _ _ _ _ _ _ _ _
    Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianCompactPointwiseDifference
