import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetLogGammaVerticalStep

/-!
# First-order comparison of actual vertical Stirling observations

Compare the actual Stirling remainder increment to its literal slope
term at one common clock. The error keeps the separate quadratic
logarithm and log-Gamma bounds and the explicit normalization costs.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLogVerticalStep (step)
open GaussianBinetLogGammaVerticalStep (scaled_distance step_bound dyadicCost)
open GaussianBinetStirlingRemainder (offset)
open GaussianBinetStirlingSlopeBound (correction)
open GaussianBinetStirlingUnitDifference (remainderBudget remainder_error)
open GaussianBinetStirlingUnitDifferenceAlgebra (rawRemainder)
open GaussianBinetStirlingVerticalAlgebra (remainder_difference linear_expression)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianLogGammaEulerCofinal (canonicalData)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerTaylorRows (coefficient)
open GaussianNameArithmetic (sum_distance)
open GaussianNamedDifference (difference_distance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (bounded_product reciprocal)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRightHalfPlaneLogarithmIncrementMargin (smallStep)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "R" => GaussianBinetStirlingRemainder.nameF
local notation "rd" => GaussianBinetStirlingRemainder.data
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithm.data
local notation "G" => GaussianLogGammaEulerCofinal.nameF
local notation "P" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "pd" => GaussianLogGammaEulerDigammaFractionsCofinal.data

def logError (p A H : PTm n) : PTm n := num 4*H*H*unit p+num 9*(A*A)
def gammaError (p A B D sign H K : PTm n) : PTm n := coefficient H K*unit p+dyadicCost A B D sign H*(D*D)
def errorDenominator (p A D : PTm n) : PTm n := (D*D)*(A*A)*unit p
def errorNumerator (p A B D sign H K W : PTm n) : PTm n :=
  (remainderBudget A (B+H) D sign+remainderBudget A B D sign)*((D*D)*(A*A))+
    gammaError p A B D sign H K*(A*A)+H*(H*A*unit p+logError p A H)*D+
    W*logError p A H*(D*D)

def linearTerm (p A B D sign H : PTm n) : PTm n :=
  qmul (step H D sign)
    (qadd (qsub (ap2 P p (pd A B D sign)) (ap2 L p (ld A B D sign))) (correction A B D sign))

theorem sample_error (p A B D sign H K C W x : PTm n)
    (h : Γ ⊢[PRAAx] source A D sign) (hK : Γ ⊢[PRAAx] le one K) (hm : Γ ⊢[PRAAx] le D (K*A))
    (hsize : Γ ⊢[PRAAx] le (A+B+A+(B+H)) (C*D)) (hs : Γ ⊢[PRAAx] smallStep H K C D)
    (hw : Γ ⊢[PRAAx] bounded (offset A B D sign) W one) :
    Γ ⊢[PRAAx] distanceBounded (qsub (ap2 R p (rd A (B+H) D sign x)) (ap2 R p (rd A B D sign x)))
      (linearTerm p A B D sign H) (errorNumerator p A B D sign H K W) (errorDenominator p A D) := by
  let u := unit p
  let DD := D*D
  let AA := A*A
  let V := errorDenominator p A D
  let v := AA*u
  let z := argument A B D sign
  let e := step H D sign
  let o := offset A B D sign
  let g := ap2 G p (canonicalData A B D sign)
  let k := ap2 G p (canonicalData A (B+H) D sign)
  let l := ap2 L p (ld A B D sign)
  let m := ap2 L p (ld A (B+H) D sign)
  let ψ := ap2 P p (pd A B D sign)
  let r := reciprocal z
  let c := ap2 GaussianStirlingConstant.nameF p (GaussianStirlingConstant.nameData x)
  let f := rawRemainder A B D sign g l c
  let t := rawRemainder A (B+H) D sign k m c
  let hA := h.andE₁.andE₁
  let hD := h.andE₂
  have hu := unit_positive (Γ := Γ) p
  have hAA := positive_product A A hA hA
  have hDD := positive_product D D hD hD
  have hv := positive_product AA u hAA hu
  have hV := positive_product (DD*AA) u (positive_product DD AA hDD hAA) hu
  have hn := step_bound D sign H hD h.andE₁.andE₂
  have eLog : Γ ⊢[PRAAx] distanceBounded (qsub m l) (qmul e r) (logError p A H) v :=
    GaussianBinetLogVerticalStep.sample_error p A B D sign H K C h hK hm hsize hs
  have hRec := GaussianRationalLowerBounds.inverse_bound z A D hA hD (GaussianBinetReciprocalRows.real_part_lower A B D sign h)
  have hr := bounded_product e r H D D A hD hA hn hRec
  have hb : Γ ⊢[PRAAx] bounded (qmul e r) (H*A*u) v :=
    bounded_radius_mono _ _ _ _ _ (positive_product D A hD hA) hv
      (by dsimp only [v,AA]; ipra_le 0) hr
  have lm := distance_triangle_same (qsub m l) (qmul e r) qzero _ _ v hv eLog
    ((distance_zero_iff _ _ _ hv).iffMpr hb)
  have timeDelta : Γ ⊢[PRAAx] distanceBounded m l (H*A*u+logError p A H) v :=
    (distance_zero_iff _ _ _ hv).iffMp
      (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) lm)
  have weightedLeft := scaled_distance e m l H D _ v hD hv hn timeDelta
  have weightedRight := scaled_distance o (qsub m l) (qmul e r) W one _ v (le_refl one) hv hw eLog
  have leftBound : Γ ⊢[PRAAx] distanceBounded (qmul e m) (qmul e l) (H*(H*A*u+logError p A H)*D) V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product D v hD hv) hV
      (by dsimp only [V,errorDenominator,v,AA,u]; ipra_le 0) weightedLeft
  have rightBound : Γ ⊢[PRAAx] distanceBounded (qmul o (qsub m l)) (qmul o (qmul e r)) (W*logError p A H*DD) V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product one v (le_refl one) hv) hV
      (by dsimp only [V,errorDenominator,v,AA,u,DD]; ipra_le 0) weightedRight
  have logBoth := sum_distance _ _ _ _ _ _ V hV leftBound rightBound
  have ga := GaussianBinetLogGammaVerticalStep.sample_error p A B D sign H K C h hK hm hsize hs
  have gammaBound : Γ ⊢[PRAAx] distanceBounded (qsub k g) (qmul e ψ) (gammaError p A B D sign H K*AA) V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product DD u hDD hu) hV
      (by dsimp only [V,errorDenominator,DD,AA,u,gammaError]; ipra_le 0) ga
  have exactBound := sum_distance _ _ e e _ _ V hV
    (difference_distance _ _ _ _ _ _ V hV gammaBound logBoth) (distance_refl_zero e V hV)
  have obs := difference_distance (ap2 R p (rd A (B+H) D sign x)) t (ap2 R p (rd A B D sign x)) f _ _ u hu
    (remainder_error p A (B+H) D sign x h) (remainder_error p A B D sign x h)
  have first : Γ ⊢[PRAAx] distanceBounded (qsub (ap2 R p (rd A (B+H) D sign x)) (ap2 R p (rd A B D sign x)))
      (qsub t f) ((remainderBudget A (B+H) D sign+remainderBudget A B D sign)*(DD*AA)) V :=
    distance_radius_mono _ _ _ _ _ _ hu hV (by dsimp only [V,errorDenominator,DD,AA,u]; ipra_le 0) obs
  have second := distance_congr (remainder_difference A B D sign H g l k m c h).eqSymm
    (linear_expression A B D sign H ψ l h) (.eqRefl _) (.eqRefl _) exactBound
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [errorNumerator,DD,AA,u]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ (qsub t f) _ _ _ V hV first second)

theorem actual_complex_Stirling_vertical_first_order_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let p := var 0
     let A := var 1
     let B := var 2
     let D := var 3
     let sign := var 4
     let H := var 5
     let K := var 6
     let C := var 7
     let W := var 8
     let x := var 9
     source A D sign ⟶ le one K ⟶ le D (K*A) ⟶ le (A+B+A+(B+H)) (C*D) ⟶
       smallStep H K C D ⟶ bounded (offset A B D sign) W one ⟶
       distanceBounded (qsub (ap2 R p (rd A (B+H) D sign x)) (ap2 R p (rd A B D sign x)))
         (linearTerm p A B D sign H) (errorNumerator p A B D sign H K W) (errorDenominator p A D)) :=
  closeUniv 10 (.impI (.impI (.impI (.impI (.impI (.impI
    (sample_error _ _ _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk.wk Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalStep
