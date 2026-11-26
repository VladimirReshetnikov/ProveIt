import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailRootedMajorant
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerNamedLowerTail
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinGrid
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.EndpointBounds.GaussianGammaZetaMellinOriginBound

/-!
# The original Mellin lower tail on a powered cutoff window

Use the actual Mellin observations at the positive powered right tags,
and transfer their bounds to the affine compact quadrature. A cofinal
refinement then gives the original compact name's lower-tail budget.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinLowerRooted

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (mesh precision quadrature sampledModulus)
open GaussianEulerLowerCofinalQuadrature (rootMesh transformed)
open GaussianEulerLowerPowerCoefficients (source)
open GaussianEulerLowerTailFiniteBudget (residual scale numerator denominator)
open GaussianEulerLowerTailPartition (root_right_guard totalWidth)
open GaussianEulerLowerTailRootGrid (rootDenominator rootNumerator timeNumerator timeDenominator)
open GaussianEulerLowerTailLocalComparison (rightTime)
open GaussianEulerLowerTailRootedMajorant (quadratureValue rooted_modulus rooted_width_positive rightBounds)
open GaussianGammaCompactCutoffGeometry (lowerWidth lower_positive)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen height)
open GaussianGammaZetaMellinGrid (evaluatorF fixedData sample_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem right_sample_bound (i s N p q k z R B : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (rightTime i N p q (succ k) R) (fixedData (shifted z B) B))
      (pw (rootDenominator N q (succ k) R) k*unit s+num 3*pw (rootNumerator (succ i) N p q) k)
      (pw (rootNumerator (succ i) N p q) k*unit s) := by
  let A := succ k
  let a := rootNumerator (succ i) N p q
  let b := rootDenominator N q A R
  have pos := root_right_guard i N p q A R hN hpq hi
  have hb : Γ ⊢[PRAAx] le one b := positive_product _ _ (unit_positive _) hN
  have hs : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R B A a b :=
    .andI h (.andI (.andI pos.andE₁ hb) pos.andE₂)
  have read := sample_at (Γ := Γ) s (shifted z B) B (pw a A) (pw b A)
  have e := pred_succ (Γ := Γ) k
  have ea := congrAp2 powF e (.eqRefl a)
  have eb := congrAp2 powF e (.eqRefl b)
  exact bound_congr read.eqSymm (congrAdd (congrMul eb (.eqRefl _)) (congrMul (.eqRefl _) ea))
    (congrMul ea (.eqRefl _)) (GaussianGammaZetaMellinOriginBound.origin_bound s z R B A a b hs)

theorem right_bounds (s N p q k z R B : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hpq : Γ ⊢[PRAAx] le p q) (h : Γ ⊢[PRAAx] source z R B (succ k)) :
    Γ ⊢[PRAAx] rightBounds evaluatorF (fixedData (shifted z B) B) s N p q k R one := by
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh N) :: Γ.map Fm.shift
  have hN' : Δ ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hN.shift.wk
  have hpq' : Δ ⊢[PRAAx] le (sh p) (sh q) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hpq.shift.wk
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (succ (sh k)) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift.wk
  have raw := right_sample_bound (var 0) (sh s) (sh N) (sh p) (sh q) (sh k) (sh z) (sh R) (sh B)
    hN' hpq' Prf.hyp0 hs
  simpa only [Δ,sh,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,fixedData,
    subst_pairT,GaussianGammaEulerHeadShift.subst_shifted] using
    bound_congr (.eqRefl _) (one_mul _).eqSymm (.eqRefl _) raw

private theorem transformed_grid (F : PR 3) (t p q k R L T x : PTm n) : Γ ⊢[PRAAx]
    quadratureValue F (precision t T) (rootMesh t L T) p q k R x ≐
      transformed F t (succ k) (lowerWidth p q (succ k)) (etaDen q (succ k) R) L T x := by
  let A := succ k
  let N := rootMesh t L T
  let a := timeNumerator zero N p q A
  let C := totalWidth N p q A
  let E := timeDenominator N q A R
  let W := lowerWidth p q A*pw N A
  let V := etaDen q A R*pw N A
  let s := precision t T
  have ha : Γ ⊢[PRAAx] a ≐ pw N A := GaussianEulerLowerTailRootGrid.time_first N p q A
  have hc : Γ ⊢[PRAAx] C ≐ W := GaussianEulerLowerTailRootGrid.time_width N p q A
  have he : Γ ⊢[PRAAx] E ≐ V := GaussianEulerLowerTailRootGrid.time_denominator N q A R
  simpa only [quadratureValue,transformed,GaussianEulerLowerCofinalQuadrature.count,GaussianEulerLowerCofinalQuadrature.scale,
    GaussianCompactRiemannName.subst_quadrature,Syn.subst_var,Matrix.cons_val,a,C,E,W,V,s,N,A] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
      (quadrature F (var 0) (var 1) (var 2) (var 1) (var 3) (var 4) : PTm 5)
      (σ := ![s,C,a,E,x]) (σ' := ![s,W,pw N A,V,x])
      (fun j => by fin_cases j; exact .eqRefl _; exact hc; exact ha; exact he; exact .eqRefl _)

theorem transformed_bound (t p q k z R B L T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) (hpq : Γ ⊢[PRAAx] lt p q)
    (hm : Γ ⊢[PRAAx] sampledModulus evaluatorF one (lowerWidth p q (succ k)) (etaDen q (succ k) R) L
      (fixedData (shifted z B) B)) : Γ ⊢[PRAAx]
    bounded (transformed evaluatorF t (succ k) (lowerWidth p q (succ k)) (etaDen q (succ k) R) L T
      (fixedData (shifted z B) B)) (two*numerator t p q k R L) (denominator t p k R) := by
  let N := rootMesh t L T
  let s := precision t T
  let x := fixedData (shifted z B) B
  have hN : Γ ⊢[PRAAx] le (unit t) N :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (unit t) (GaussianCompactRiemannName.mesh_positive t L T))
  have hN₁ : Γ ⊢[PRAAx] le one N := le_trans (unit_positive t) hN
  have hs : Γ ⊢[PRAAx] le (unit t) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right t T) (le_add_right _ _))
  have raw := GaussianEulerLowerTailRootedMajorant.original_cofinal_bound evaluatorF x s t N p q k R one L
    (le_of_lt hpq) hN hs (rooted_width_positive N p q k hN₁ hpq)
    (rooted_modulus evaluatorF x N p q k R L hN₁ hm) (right_bounds s N p q k z R B hN₁ (le_of_lt hpq) h)
  exact bound_congr (transformed_grid evaluatorF t p q k R L T x) (by ipra_ring) (.eqRefl _) raw

/-- The actual compact name has a lower-tail bound independent of any
larger endpoint or a finite geometric cutoff. -/
theorem original_observation_bound (r p q k z R B L T : PTm n)
    (h : Γ ⊢[PRAAx] source z R B (succ k)) (hpq : Γ ⊢[PRAAx] lt p q)
    (hs : Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF one (lowerWidth p q (succ k)) (etaDen q (succ k) R)
      L T (fixedData (shifted z B) B)) : Γ ⊢[PRAAx]
    bounded
      (ap2 (GaussianCompactRiemannName.nameF evaluatorF) r
        (GaussianCompactRiemannName.data one (lowerWidth p q (succ k)) (etaDen q (succ k) R) L T (fixedData (shifted z B) B)))
      ((two*succ k)*unit r+unit (height p (succ k) R)) (unit (height p (succ k) R)*unit r) := by
  let A := succ k
  let C := lowerWidth p q A
  let E := etaDen q A R
  let H := unit (height p A R)
  let x := fixedData (shifted z B) B
  let K := two*residual (scale p q k) L
  let y := ap2 (GaussianCompactRiemannName.nameF evaluatorF) r (GaussianCompactRiemannName.data one C E L T x)
  let U := (two*A)*unit r+H
  let V := H*unit r
  let t := GaussianRationalSlackRemoval.precision y U V (K+two)
  have hH : Γ ⊢[PRAAx] le one H := unit_positive _
  have hD : Γ ⊢[PRAAx] le one (unit t*unit r) := positive_product _ _ (unit_positive t) (unit_positive r)
  have input : Γ ⊢[PRAAx] GaussianEulerLowerCofinalQuadrature.input evaluatorF A C E L T x :=
    .andI (zero_lt_succ k) (.andI (lower_positive p q A (zero_lt_succ k) hpq) hs)
  have raw := GaussianEulerLowerCofinalQuadrature.observations evaluatorF t r A C E L T x input
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF r one C E L T x
  have d := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) read.eqSymm (.eqRefl _) (.eqRefl _) raw
  have b := transformed_bound t p q k z R B L T h hpq hs.andE₂.andE₂.andE₂
  have b' : Γ ⊢[PRAAx] bounded (transformed evaluatorF t A C E L T x) ((two*A)*unit t+K*H) (H*unit t) :=
    bound_congr (.eqRefl _) (by dsimp only [A,K,H]; unfold numerator GaussianEulerLowerTailFiniteBudget.nativeNumerator; ipra_ring)
      (.eqRefl _) b
  have sm := GaussianEulerNamedLowerTail.compared_bound_to_slack y _ (two*A) H K r t hH
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hD d) b'
  exact slack_removal_at y U V (K+two) (positive_product _ _ hH (unit_positive r)) sm

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinLowerRooted
