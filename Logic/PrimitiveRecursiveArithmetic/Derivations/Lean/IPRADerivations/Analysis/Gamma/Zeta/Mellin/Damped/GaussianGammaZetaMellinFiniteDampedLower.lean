import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteDampedModulus
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Compact.GaussianGammaZetaMellinGeometricEnvelope
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailRootedMajorant
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerNamedLowerTail
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactAlignedSplit

/-!
# Uniform lower-tail bound for the original finite damped rows

The finite evaluator is compared at the powered right tags to the
actual geometric prefix. Its lower-tail coefficient is independent
of the number of retained damped rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerLowerPowerCoefficients (source)
open GaussianEulerLowerTailLocalComparison (rightTime)
open GaussianEulerLowerTailPartition (root_right_guard)
open GaussianEulerLowerTailRootGrid (rootNumerator rootDenominator)
open GaussianEulerLowerTailRootedMajorant (quadratureValue rightBounds rooted_modulus rooted_width_positive)
open GaussianGammaCompactCutoffGeometry (lowerWidth)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen)
open GaussianGammaZetaMellinFiniteDampedEvaluator (evaluatorF data budget comparisonClock geometric_point_error)
open GaussianGammaZetaMellinFiniteDampedModulus (lipschitz)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem sample_bound (s z R₀ R B A x y H T N : PTm n)
    (hz : Γ ⊢[PRAAx] source z R₀ B A)
    (hr : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (shifted z B) R B H)
    (hx : Γ ⊢[PRAAx] le one x) (hy : Γ ⊢[PRAAx] le one y) (hxy : Γ ⊢[PRAAx] le x y)
    (hd : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (pw x A) (pw y A) H T) : Γ ⊢[PRAAx]
    bounded (ap3 evaluatorF s (pairT (pw x A) (pw y A)) (data (shifted z B) B N (budget R H T N)))
      (num 3*(pw y (LeanProofs.IPRA.PTm.pred A)*unit s+num 3*pw x (LeanProofs.IPRA.PTm.pred A)))
      (pw x (LeanProofs.IPRA.PTm.pred A)*unit s) := by
  let a := pw x A
  let b := pw y A
  let t := comparisonClock s R H T N a b
  let X := pw x (LeanProofs.IPRA.PTm.pred A)
  let Y := pw y (LeanProofs.IPRA.PTm.pred A)
  let U := unit s
  let V := unit t
  have hX : Γ ⊢[PRAAx] le one X := GaussianPolynomialPerturbation.power_positive _ _ hx
  have hU : Γ ⊢[PRAAx] le one U := unit_positive s
  have hV : Γ ⊢[PRAAx] le one V := unit_positive t
  have dom : Γ ⊢[PRAAx] GaussianEulerLowerPowerOrder.source z R₀ B A x y :=
    .andI hz (.andI (.andI hx hy) hxy)
  have original := GaussianGammaZetaMellinOriginBound.origin_bound t z R₀ B A x y dom
  have middle := GaussianGammaZetaMellinGeometricEnvelope.weighted_bound t (shifted z B) B a b N
    (Y*V+num 3*X) (X*V) hd.andE₁.andE₁ hd.andE₁.andE₂ (positive_product _ _ hX hV) original
  have gap := geometric_point_error s (shifted z B) R B a b H T N hr hd
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hU (positive_product _ _ hX hV) gap middle
  have later : Γ ⊢[PRAAx] le U V :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right _ _) (le_add_right _ _))
  refine bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU (positive_product _ _ hX hV))
    (positive_product _ _ hX hU) ?_ raw
  change Γ ⊢[PRAAx] le ((two*(X*V)+(Y*V+num 3*X)*two*U)*(X*U))
    ((num 3*(Y*U+num 3*X))*(U*(X*V)))
  unfold num two
  ipra_le 6*𝔞(X)*𝔞(X)*𝔞(U)*sl later + 𝔞(Y)*𝔞(U)*𝔞(X)*𝔞(U)*𝔞(V) + 𝔞(X)*𝔞(X)*𝔞(U)*𝔞(V)

private theorem right_sample_bound (i s M p q k z R₀ R B T N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hpq : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i M)
    (hz : Γ ⊢[PRAAx] source z R₀ B (succ k)) (hT : Γ ⊢[PRAAx] le one T)
    (hr : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (shifted z B) R B (etaDen q (succ k) R₀)) :
    let H := etaDen q (succ k) R₀
    Γ ⊢[PRAAx] bounded (ap3 evaluatorF s (rightTime i M p q (succ k) R₀) (data (shifted z B) B N (budget R H T N)))
      (num 3*(pw (rootDenominator M q (succ k) R₀) k*unit s+num 3*pw (rootNumerator (succ i) M p q) k))
      (pw (rootNumerator (succ i) M p q) k*unit s) := by
  intro H
  let A := succ k
  let x := rootNumerator (succ i) M p q
  let y := rootDenominator M q A R₀
  let a := pw x A
  let b := pw y A
  have hx := root_right_guard i M p q A R₀ hM hpq hi
  have hy : Γ ⊢[PRAAx] le one y := positive_product _ _ (unit_positive _) hM
  have ha := GaussianPolynomialPerturbation.power_positive x A hx.andE₁
  have hb := GaussianPolynomialPerturbation.power_positive y A hy
  have lb : Γ ⊢[PRAAx] le (pw M A) a :=
    pw_le_pw A (le_add_right M (GaussianEulerLowerTailPartition.rootStep p q*succ i))
  have hLeft : Γ ⊢[PRAAx] le b (H*a) :=
    le_congr (GaussianEulerLowerTailRootGrid.time_denominator M q A R₀).eqSymm (.eqRefl _)
      (le_congr (mul_comm (pw M A) H) (mul_comm a H) (mul_le_mul_right H lb))
  have hUpper : Γ ⊢[PRAAx] le a (T*b) :=
    le_trans (pw_le_pw A hx.andE₂) (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right b hT))
  have hd : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b H T :=
    .andI (.andI ha hb) (.andI hLeft hUpper)
  have e := pred_succ (Γ := Γ) k
  have ex := congrAp2 powF e (.eqRefl x)
  have ey := congrAp2 powF e (.eqRefl y)
  exact bound_congr (.eqRefl _) (congrMul (.eqRefl _) (congrAdd
    (congrMul ey (.eqRefl _)) (congrMul (.eqRefl _) ex))) (congrMul ex (.eqRefl _))
    (sample_bound s z R₀ R B A x y H T N hz hr hx.andE₁ hy hx.andE₂ hd)

theorem right_bounds (s M p q k z R₀ R B T N : PTm n)
    (hM : Γ ⊢[PRAAx] le one M) (hpq : Γ ⊢[PRAAx] le p q)
    (hz : Γ ⊢[PRAAx] source z R₀ B (succ k)) (hT : Γ ⊢[PRAAx] le one T)
    (hr : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source (shifted z B) R B (etaDen q (succ k) R₀)) :
    Γ ⊢[PRAAx] rightBounds evaluatorF (data (shifted z B) B N (budget R (etaDen q (succ k) R₀) T N)) s M p q k R₀ (num 3) := by
  refine .allI (.impI ?_)
  let sh (u : PTm n) := Syn.shift u
  let Δ := lt (var 0) (sh M) :: Γ.map Fm.shift
  have hM' : Δ ⊢[PRAAx] le one (sh M) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hM.shift.wk
  have hpq' : Δ ⊢[PRAAx] le (sh p) (sh q) := by simpa [Fm.shift,Syn.shift,Δ,sh] using hpq.shift.wk
  have hz' : Δ ⊢[PRAAx] source (sh z) (sh R₀) (sh B) (succ (sh k)) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using hz.shift.wk
  have hT' : Δ ⊢[PRAAx] le one (sh T) := by simpa [Fm.shift,Syn.shift,Δ,sh,one] using hT.shift.wk
  have hr' : Δ ⊢[PRAAx]
      GaussianEulerExponentCompactBounds.source (shifted (sh z) (sh B)) (sh R) (sh B) (etaDen (sh q) (succ (sh k)) (sh R₀)) := by
    simpa [Fm.shift,Syn.shift,Δ,sh,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
      using hr.shift.wk
  simpa [Fm.shift,Syn.shift,Δ,sh,etaDen,GaussianGammaIntegralCutoffs.height,GaussianGammaIntegralCutoffs.tailCoefficient]
    using right_sample_bound (var 0) (sh s) (sh M) (sh p) (sh q) (sh k) (sh z) (sh R₀) (sh R) (sh B) (sh T) (sh N)
      hM' hpq' Prf.hyp0 hz' hT' hr'

theorem original_cofinal_bound (s t M p q k z R₀ R B T N : PTm n)
    (hpq : Γ ⊢[PRAAx] lt p q) (hM : Γ ⊢[PRAAx] le (unit t) M) (hs : Γ ⊢[PRAAx] le (unit t) (unit s))
    (hz : Γ ⊢[PRAAx] source z R₀ B (succ k)) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource (shifted z B) R B one
      (lowerWidth p q (succ k)) (etaDen q (succ k) R₀) T) :
    let E := etaDen q (succ k) R₀
    let L := lipschitz N R E T
    Γ ⊢[PRAAx] bounded (quadratureValue evaluatorF s M p q k R₀ (data (shifted z B) B N (budget R E T N)))
      (num 4*GaussianEulerLowerTailFiniteBudget.numerator t p q k R₀ L)
      (GaussianEulerLowerTailFiniteBudget.denominator t p k R₀) := by
  intro E L
  let Q := budget R E T N
  let x := data (shifted z B) B N Q
  have hM₁ := le_trans (unit_positive t) hM
  have hQ : Γ ⊢[PRAAx] le N Q := le_of_eq_add (d := N*GaussianGammaZetaMellinDampedPoint.cost R E T)
    (by unfold Q budget; ipra_ring)
  have hm := GaussianGammaZetaMellinFiniteDampedModulus.original_sampled_modulus _ _ _ N Q _ _ _ _ h hQ
  have rooted := rooted_modulus evaluatorF x M p q k R₀ L hM₁ hm
  have right := right_bounds s M p q k z R₀ R B T N hM₁ (le_of_lt hpq) hz hT h.andE₁
  exact bound_congr (.eqRefl _) (by unfold num; ipra_ring) (.eqRefl _)
    (GaussianEulerLowerTailRootedMajorant.original_cofinal_bound evaluatorF x s t M p q k R₀ (num 3) L (le_of_lt hpq) hM hs
      (rooted_width_positive M p q k hM₁ hpq) rooted right)

/-- The original compact name of the finite damped evaluator has a lower
tail bounded independently of the retained geometric count. -/
theorem original_observation_bound (r p q k z R₀ R B T N : PTm n)
    (hpq : Γ ⊢[PRAAx] lt p q) (hz : Γ ⊢[PRAAx] source z R₀ B (succ k)) (hT : Γ ⊢[PRAAx] le one T)
    (h : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.intervalSource (shifted z B) R B one
      (lowerWidth p q (succ k)) (etaDen q (succ k) R₀) T) :
    let A := succ k
    let E := etaDen q A R₀
    let L := lipschitz N R E T
    let H := unit (GaussianGammaIntegralCutoffs.height p A R₀)
    let x := data (shifted z B) B N (budget R E T N)
    Γ ⊢[PRAAx] bounded
      (ap2 (GaussianCompactRiemannName.nameF evaluatorF) r
        (GaussianCompactRiemannName.data one (lowerWidth p q A) E L T x))
      ((num 4*A)*unit r+H) (H*unit r) := by
  intro A E L H x
  let C := lowerWidth p q A
  let Q := budget R E T N
  let y := ap2 (GaussianCompactRiemannName.nameF evaluatorF) r (GaussianCompactRiemannName.data one C E L T x)
  let K := num 4*GaussianEulerLowerTailFiniteBudget.residual (GaussianEulerLowerTailFiniteBudget.scale p q k) L
  let U := (num 4*A)*unit r+H
  let V := H*unit r
  let t := GaussianRationalSlackRemoval.precision y U V (K+two)
  let M := GaussianEulerLowerCofinalQuadrature.rootMesh t L T
  let s := GaussianCompactRiemannName.precision t T
  let w := GaussianEulerLowerCofinalQuadrature.transformed evaluatorF t A C E L T x
  have hQ : Γ ⊢[PRAAx] le N Q := le_of_eq_add (d := N*GaussianGammaZetaMellinDampedPoint.cost R E T)
    (by unfold Q budget; ipra_ring)
  have hm := GaussianGammaZetaMellinFiniteDampedModulus.original_sampled_modulus _ _ _ N Q _ _ _ _ h hQ
  have input : Γ ⊢[PRAAx] GaussianCompactRiemannName.input evaluatorF one C E L T x :=
    .andI (le_refl one) (.andI h.andE₁.andE₂.andE₁
      (.andI (le_trans (le_add_left _ _) h.andE₂.andE₂) hm))
  have hA : Γ ⊢[PRAAx] le one A := zero_lt_succ k
  have hC := GaussianGammaCompactCutoffGeometry.lower_positive p q A hA hpq
  have hM : Γ ⊢[PRAAx] le (unit t) M :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (unit t) (GaussianCompactRiemannName.mesh_positive t L T))
  have hs : Γ ⊢[PRAAx] le (unit t) (unit s) :=
    GaussianExponentialReference.unit_monotone (le_trans (le_add_right t T) (le_add_right _ _))
  have b := original_cofinal_bound s t M p q k z R₀ R B T N hpq hM hs hz hT h
  have size := GaussianEulerLowerTailRootGrid.time_width (Γ := Γ) M p q A
  have start := GaussianEulerLowerTailRootGrid.time_first (Γ := Γ) M p q A
  have denom := GaussianEulerLowerTailRootGrid.time_denominator (Γ := Γ) M q A R₀
  have read : Γ ⊢[PRAAx] quadratureValue evaluatorF s M p q k R₀ x ≐ w :=
    GaussianCompactAlignedSplit.quadrature_congr evaluatorF (.eqRefl s) size start size denom (.eqRefl x)
  have b' : Γ ⊢[PRAAx] bounded w ((num 4*A)*unit t+K*H) (H*unit t) :=
    bound_congr read (by
      dsimp only [K,H,A]
      unfold GaussianEulerLowerTailFiniteBudget.numerator GaussianEulerLowerTailFiniteBudget.nativeNumerator
      ipra_ring) (.eqRefl _) b
  have cmp := GaussianEulerLowerCofinalQuadrature.observations evaluatorF t r A C E L T x (.andI hA (.andI hC input))
  have dy := GaussianCompactRiemannName.name_at (Γ := Γ) evaluatorF r one C E L T x
  have d := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) dy.eqSymm (.eqRefl _) (.eqRefl _) cmp
  have hH : Γ ⊢[PRAAx] le one H := unit_positive _
  have hd := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive r)
  have sm := GaussianEulerNamedLowerTail.compared_bound_to_slack y w (num 4*A) H K r t hH
    (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ hd d) b'
  exact GaussianRationalSlackRemoval.slack_removal_at y U V (K+two)
    (positive_product _ _ hH (unit_positive r)) sm

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinFiniteDampedLower
