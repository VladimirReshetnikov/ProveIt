import IPRADerivations.Analysis.Names.GaussianNamedGoldenRatio
import IPRADerivations.Analysis.RationalArithmetic.GaussianGoldenRatioRationalUniqueness
import IPRADerivations.Analysis.Logarithm.GaussianNamedPositiveLogarithm

/-!
# The positive named golden-ratio equation

Every certified positive regular name satisfying the quadratic identity
is equivalent to the independent affine square-root name. The only
order comparison needed is at finite rational observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioUniqueness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedGoldenRatio (onePoint)
open GaussianNamedPositiveLogarithm (source numerator denominator decoded_domain decoded_value)
open GaussianNamedDiagonalRate (diagonalRate cross_of_diagonal_rate)
open GaussianGoldenRatioRationalUniqueness (residual residual_distance)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaHalfSqrtBrackets (fraction_gap)
open GaussianNameArithmetic (addF addData multiplyF multiplyData multiplyModulus)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal diagonal_at)
open GaussianRationalHorner (qmul qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric distance_triangle_same)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "goldenF" => GaussianNamedGoldenRatio.nameF
local notation "goldenData" => GaussianNamedGoldenRatio.nameData

def quadratic (f : PR 2) (x : PTm n) : Fm PTm n :=
  crossEquivalent (multiplyF f f) (addF f constantF) (multiplyData f f x x) (addData x onePoint)

def allowance (f : PR 2) (x : PTm n) : PTm n := (multiplyModulus f f x x+one)+two+(two+one)

private theorem raw_residual (a b K U : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] distanceBounded (qmul (fraction a b) (fraction a b)) (qadd (fraction a b) onePoint) K U) :
    Γ ⊢[PRAAx] residual a b K U := by
  have square := GaussianEulerDampedTimeRate.fraction_product a b a b hb hb
  have sum : Γ ⊢[PRAAx] qadd (fraction a b) onePoint ≐ fraction (a+b) b :=
    (GaussianEulerPositivePowerChartCorrectedImage.fraction_sum a b one one hb (le_refl one)).eqTrans
    (GaussianEulerPositivePowerChartJacobian.fraction_congr (by ipra_ring) (by ipra_ring))
  have dist : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) (fraction (a+b) b) K U :=
    distance_congr square sum (.eqRefl _) (.eqRefl _) h
  have gap := fraction_gap _ _ _ _ _ _ (positive_product _ _ hb hb) hb hU dist
  exact .andI (RationalValueBounds.positive_cancel hb (le_congr (by ipra_ring) (by ipra_ring) gap.andE₁))
    (RationalValueBounds.positive_cancel hb (le_congr (by ipra_ring) (by ipra_ring) gap.andE₂))

private theorem quadratic_raw_distance (f : PR 2) (p x : PTm n)
    (reg : Γ ⊢[PRAAx] pointCN f x) (hq : Γ ⊢[PRAAx] quadratic f x) :
    Γ ⊢[PRAAx] distanceBounded (qmul (ap2 f p x) (ap2 f p x)) (qadd (ap2 f p x) onePoint)
      (allowance f x) (unit p) := by
  have hp : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  have first := distance_symmetric _ _ _ _ hp (GaussianNameRingLaws.multiply_sample_error f f x x p reg reg)
  have mid := diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ hq)
  have last := GaussianNameRingLaws.add_sample_error f constantF x onePoint p reg (constant_regular _)
  have moved := distance_congr (.eqRefl _) (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _) (constant_at p onePoint))
    (.eqRefl _) (.eqRefl _) last
  have init := distance_triangle_same _ _ _ _ _ _ hp first mid
  exact distance_triangle_same _ _ _ _ _ _ hp init moved

theorem observation_distance (f : PR 2) (p x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E T) (hq : Γ ⊢[PRAAx] quadratic f x) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 goldenF p goldenData) (two*(allowance f x+one)) (unit p) := by
  let a := numerator f p x
  let b := denominator f p x
  let c := GaussianNamedGoldenRatio.numerator p
  let d := GaussianNamedGoldenRatio.denominator p
  let t := GaussianNamedSqrtFive.clock p
  have hp : Γ ⊢[PRAAx] le one (unit p) := unit_positive p
  have hb := (decoded_domain f p x E T hs).andE₁.andE₂
  have hd := GaussianNamedGoldenRatio.denominator_positive (Γ := Γ) p
  have eq := decoded_value f p x E T hs
  have golden := GaussianNamedGoldenRatio.sample_at (Γ := Γ) p (goldenData : PTm n)
  have left := quadratic_raw_distance f p x hs.andE₁ hq
  have right := GaussianNamedGoldenRatio.raw_quadratic (Γ := Γ) p (goldenData : PTm n)
  have hr : Γ ⊢[PRAAx] le (num 3*d) (two*c) := by
    have control := (GaussianNamedSqrtFive.numerator_bounds (Γ := Γ) t).andE₁
    change Γ ⊢[PRAAx] le (num 3*(two*unit t)) (two*(unit t+GaussianNamedSqrtFive.root t))
    ipra_le 2*sl control
  have rl := raw_residual a b (allowance f x) (unit p) hb hp
    (distance_congr (GaussianRationalSyntheticDivision.qmul_congr eq.eqSymm eq.eqSymm)
      (GaussianRationalSyntheticDivision.qadd_congr eq.eqSymm (.eqRefl _)) (.eqRefl _) (.eqRefl _) left)
  have rr := raw_residual c d one (unit p) hd hp
    (distance_congr (GaussianRationalSyntheticDivision.qmul_congr golden golden)
      (GaussianRationalSyntheticDivision.qadd_congr golden (.eqRefl _)) (.eqRefl _) (.eqRefl _) right)
  exact distance_congr eq golden.eqSymm (.eqRefl _) (.eqRefl _) (residual_distance _ _ _ _ _ _ _ hb hd hp hr rl rr)

theorem root_unique (f : PR 2) (x E T : PTm n)
    (hs : Γ ⊢[PRAAx] source f x E T) (hq : Γ ⊢[PRAAx] quadratic f x) :
    Γ ⊢[PRAAx] crossEquivalent f goldenF x goldenData := by
  have diag : Γ ⊢[PRAAx] diagonalRate f goldenF x goldenData (two*(allowance f x+one)) := by
    let sh (v : PTm n) := Syn.shift v
    have hS : Γ.map Fm.shift ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by
      simpa [Fm.shift,Syn.shift,sh] using hs.shift
    have hQ : Γ.map Fm.shift ⊢[PRAAx] quadratic f (sh x) := by
      simpa [quadratic,onePoint,Fm.shift,Syn.shift,sh] using hq.shift
    refine .allI ?_
    simpa [diagonalRate,allowance,GaussianNamedGoldenRatio.nameData,Syn.shift,sh] using
      observation_distance f (var 0) (sh x) (sh E) (sh T) hS hQ
  exact cross_of_diagonal_rate _ _ _ _ _ hs.andE₁ (GaussianNamedGoldenRatio.name_regular _) diag

theorem equal_root_is_quadratic (f : PR 2) (x : PTm n) (reg : Γ ⊢[PRAAx] pointCN f x)
    (hh : Γ ⊢[PRAAx] crossEquivalent f goldenF x goldenData) : Γ ⊢[PRAAx] quadratic f x := by
  have gold := GaussianNamedGoldenRatio.name_regular (Γ := Γ) (goldenData : PTm n)
  have sq := GaussianGammaAdjacentCutoff.multiply_cross f goldenF f goldenF x goldenData x goldenData
    reg gold reg gold hh hh
  have fixed : Γ ⊢[PRAAx] pointCN constantF (onePoint : PTm n) := constant_regular _
  have add := GaussianNameArithmetic.add_equivalent f goldenF constantF constantF x goldenData onePoint onePoint
    reg gold fixed fixed (cross_to_diagonal _ _ _ _ hh) (cross_to_diagonal _ _ _ _ (cross_refl _ _ fixed))
  have center := GaussianNamedGoldenRatio.quadratic_identity (Γ := Γ) (goldenData : PTm n)
  exact cross_trans _ _ _ _ _ _ sq (cross_trans _ _ _ _ _ _ center (cross_symm _ _ _ _ add))

theorem actual_positive_named_golden_ratio_unique_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source f (var 0) (var 1) (var 2) ⟶
      Fm.iff (quadratic f (var 0)) (crossEquivalent f goldenF (var 0) goldenData)) :=
  closeUniv 3 (.impI (Prf.iffI (.impI (root_unique f _ _ _ Prf.hyp1 Prf.hyp0))
    (.impI (equal_root_is_quadratic f _ Prf.hyp1.andE₁ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedGoldenRatioUniqueness
