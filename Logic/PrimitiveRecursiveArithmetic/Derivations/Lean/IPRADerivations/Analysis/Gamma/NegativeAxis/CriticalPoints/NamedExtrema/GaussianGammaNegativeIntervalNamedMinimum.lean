import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalNamedLog
import IPRADerivations.Analysis.Gamma.NegativeAxis.Logarithms.GaussianGammaNegativeIntervalNamedLogFrozen
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalRationalProperness
import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.NamedExtrema.GaussianGammaNegativeIntervalNamedComparisonTransfer
import IPRADerivations.Analysis.Gamma.NegativeAxis.CriticalPoints.CriticalComparisons.GaussianGammaNegativeIntervalCriticalRationalComparison

/-!
# Real order from the selected negative Gamma comparisons

The critical schedule is late enough for both native logarithm
freezes. It also reads the exact selected rational on the critical
side. The finite comparisons then give named order with a fixed
margin. The zero margin applies to every admitted real input.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedMinimum

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaNegativeCriticalEndpoints (mesh)
open GaussianGammaNegativeCriticalLocation (fractionLocationF)
open GaussianGammaNegativeIntervalCriticalDerivativeZero (argumentNumerator argumentDenominator locationClock)
open GaussianGammaNegativeIntervalCriticalQuotientZero (stage)
open GaussianGammaNegativeIntervalCriticalRationalComparison (rationalMargin)
open GaussianGammaNegativeIntervalNamedInput (root_source sampleNumerator sampleDenominator frozen_guard frozen_margin)
open GaussianGammaNegativeIntervalNamedLog (nameF data clock name_regular encodedData)
open GaussianGammaNegativeIntervalNamedLogFrozen (original_frozen_rate)
open GaussianGammaNegativeIntervalStationaryBudget (comparisonCost)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedEulerUnitTime (source)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qadd qzero positive_product)
open GaussianStirlingMultiplicativeBoundsLog (fractions_order)
open GaussianStirlingTailComparison (point_add_order point_order_refl)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "L" => GaussianGammaNegativeIntervalLogAbsolute.nameF
local notation "ld" => GaussianGammaNegativeIntervalLogAbsolute.nameData

def index (p E N T : PTm n) : PTm n := p+(clock p (mesh N) N+clock p E N)+T

def gapAt (f : PR 2) (p x E N T : PTm n) : PTm n :=
  let k := index p E N T
  let s := locationClock k N
  rationalMargin (argumentNumerator k N) (argumentDenominator k N)
    (sampleNumerator f s x) (sampleDenominator f s x)

def marginAt (f : PR 2) (p x E N T m : PTm n) : Fm PTm n :=
  rationalLE (fstT m) (fstT (gapAt f p x E N T))

def marginAvailable (f : PR 2) (x E N T m : PTm n) : Fm PTm n :=
  .all (marginAt f (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift N) (Syn.shift T) (Syn.shift m))

ipra_subst index

ipra_subst marginAt [gapAt, rationalLE]

ipra_subst marginAvailable [Syn.subst_shift, Syn.shift_subst]

theorem index_bounds (p E N T : PTm n) : Γ ⊢[PRAAx]
    le p (index p E N T) ⋏ (le T (index p E N T) ⋏
      (le (clock p (mesh N) N) (index p E N T) ⋏ le (clock p E N) (index p E N T))) := by
  have h := le_add_right (Γ := Γ) (p+(clock p (mesh N) N+clock p E N)) T
  exact .andI (le_trans (le_add_right _ _) h) (.andI (le_add_left _ _) (.andI
    (le_trans (le_add_right _ _) (le_trans (le_add_left _ _) h))
    (le_trans (le_add_left _ _) (le_trans (le_add_left _ _) h))))

theorem location_clock_later (k N : PTm n) : Γ ⊢[PRAAx] le k (locationClock k N) := by
  unfold locationClock GaussianGammaNegativeCriticalLocationZero.inner GaussianGammaNegativeIntervalCriticalDerivativeZero.evaluationClock
    GaussianFastValueCut.exponent
  exact le_trans (le_trans (le_succ_self _) (le_succ_self _))
    (le_trans (le_add_right _ _) (le_add_right _ _))

theorem margin_at (f : PR 2) (p x E N T m : PTm n) (h : Γ ⊢[PRAAx] marginAvailable f x E N T m) :
    Γ ⊢[PRAAx] marginAt f p x E N T m := by
  simpa only [marginAvailable,subst_marginAt,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem selected_diagonal (f : PR 2) (p x E N T m : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (hm : Γ ⊢[PRAAx] marginAt f p x E N T m) :
    Γ ⊢[PRAAx] RationalValueBounds.upper
      (fstT (ap2 (addF constantF (nameF fractionLocationF)) p (addData m (data N (mesh N) N))))
      (fstT (ap2 (nameF f) p (data x E N))) (comparisonCost N two+num 11) (unit p) := by
  let k := index p E N T
  let s := locationClock k N
  let a := argumentNumerator k N
  let b := argumentDenominator k N
  let c := sampleNumerator f s x
  let d := sampleDenominator f s x
  let u := data N (mesh N) N
  let v := data x E N
  let K := mesh N+E
  have bd := index_bounds (Γ := Γ) p E N T
  have late := location_clock_later (Γ := Γ) k N
  have hf := frozen_guard f s x E hs
  have early := frozen_margin f s x E hs
  have eK : Γ ⊢[PRAAx] le E K := le_add_left _ _
  have hK : Γ ⊢[PRAAx] GaussianGammaNegativeIntervalChordInverse.poleMargin c d K := by
    exact .andI (le_trans early.andE₁ (mul_le_mul_right c eK))
      (le_trans early.andE₂ (mul_le_mul_right (LeanProofs.IPRA.PTm.monus d c) eK))
  have native := GaussianGammaNegativeIntervalCriticalRationalComparison.selected_comparison p p k c d N K hf
    (le_add_right _ _) hK
  have grow := GaussianStirlingTailComparison.point_add_order m (rationalMargin a b c d)
    (ap2 L p (ld a b N)) (ap2 L p (ld a b N)) hm (point_order_refl _)
  have mid := RationalValueBounds.upper_order_left _ _ _ _ _ grow native
  have hu := unit_positive (Γ := Γ) p
  have hl := original_frozen_rate fractionLocationF p s N (mesh N) N (root_source N)
    (le_trans bd.andE₂.andE₂.andE₁ late)
  have hleft := GaussianNamedRateTransport.transport (nameF fractionLocationF) L (nameF fractionLocationF) L
    u (encodedData fractionLocationF s N N) u (ld a b N) one (unit p) hu hl
    (cross_refl _ _ (name_regular fractionLocationF N (mesh N) N (root_source N)))
    (cross_symm _ _ _ _ (GaussianGammaNegativeIntervalRationalProperness.root_log_cross s N))
  have hright := original_frozen_rate f p s x E N hs (le_trans bd.andE₂.andE₂.andE₂ late)
  have hW : Γ ⊢[PRAAx] le (unit p) (unit (stage k)) :=
    GaussianExponentialReference.unit_monotone (le_trans bd.andE₁
      (le_trans (le_succ_self _) (le_succ_self _)))
  exact GaussianGammaNegativeIntervalNamedComparisonTransfer.diagonal
    (nameF fractionLocationF) (nameF f) L p (unit (stage k)) u v (ld a b N) (ld c d N) m (comparisonCost N two)
    (name_regular fractionLocationF N (mesh N) N (root_source N)) hW hleft hright mid

theorem order_with_margin (f : PR 2) (x E N T m : PTm n) (hs : Γ ⊢[PRAAx] source f x E)
    (hm : Γ ⊢[PRAAx] marginAvailable f x E N T m) : Γ ⊢[PRAAx]
    realOrder (addF constantF (nameF fractionLocationF)) (nameF f)
      (addData m (data N (mesh N) N)) (data x E N) := by
  have reg := name_regular (Γ := Γ) fractionLocationF N (mesh N) N (root_source N)
  apply order_from_envelope _ _ _ _ (comparisonCost N two+num 11)
    (GaussianNameArithmetic.add_fast _ _ _ _ (GaussianGammaCanonicalExponent.constant_regular m) reg)
    (name_regular f x E N hs)
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let sh (z : PTm n) := Syn.shift z
  have h₁ : Δ ⊢[PRAAx] source f (sh x) (sh E) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hs.shift
  have h₂ : Δ ⊢[PRAAx] marginAvailable f (sh x) (sh E) (sh N) (sh T) (sh m) := by
    simpa only [Δ,sh,Fm.shift,Syn.shift,subst_marginAvailable] using hm.shift
  simpa only [envelope,Syn.shift,sh,GaussianNameArithmetic.subst_addData,
    GaussianGammaNegativeIntervalNamedLog.subst_data,GaussianGammaNegativeCriticalEndpoints.subst_mesh,
    GaussianGammaNegativeIntervalStationaryBudget.comparisonCost,
    GaussianGammaNegativeIntervalLogAbsoluteRetiming.margin,GaussianGammaNegativeIntervalUniformLower.lowerDenominator,
    GaussianGammaNegativeIntervalUniformLower.productBound,GaussianGammaNegativeProductDerivativeRate.subst_productCap,
    GaussianStirlingGammaLogarithm.gammaMargin,two,one,PTm.subst_add,PTm.subst_mul,PTm.subst_num,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    selected_diagonal f (var 0) (sh x) (sh E) (sh N) (sh T) (sh m) h₁
      (margin_at f (var 0) (sh x) (sh E) (sh N) (sh T) (sh m) h₂)

theorem zero_margin_at (f : PR 2) (p x E N T : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] marginAt f p x E N T qzero := by
  let k := index p E N T
  let s := locationClock k N
  let a := argumentNumerator k N
  let b := argumentDenominator k N
  let c := sampleNumerator f s x
  let d := sampleDenominator f s x
  let J := GaussianGammaMinimumChord.absDelta (d*a) (b*c)
  let D := num 16*(b*d)*(b*d)
  have base := GaussianGammaNegativeIntervalCriticalComparison.base_guard (Γ := Γ) k N
  have comp := frozen_guard f s x E hs
  have hd := positive_product _ _ (le_trans base.andE₁ (le_of_lt base.andE₂))
    (le_trans comp.andE₁ (le_of_lt comp.andE₂))
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _
    (positive_product _ _ (by ipra_le 15) hd) hd
  have lo := fractions_order zero one (J*J) D (le_refl one) hD (by ipra_le 𝔞(J)*𝔞(J))
  exact rationalLE_congr (congrFst (GaussianGammaRationalWendelBoundary.fraction_zero _ (le_refl one))) (.eqRefl _) lo

theorem log_minimum (f : PR 2) (x E N : PTm n) (hs : Γ ⊢[PRAAx] source f x E) :
    Γ ⊢[PRAAx] realOrder (nameF fractionLocationF) (nameF f) (data N (mesh N) N) (data x E N) := by
  have usable : Γ ⊢[PRAAx] marginAvailable f x E N zero qzero := by
    refine .allI ?_
    have hh : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift E) := by
      simpa only [Fm.shift,Syn.shift,GaussianNamedEulerUnitTime.subst_source] using hs.shift
    simpa only [marginAvailable,Syn.shift,ConciseIPRA.PTm.subst_zero,GaussianRationalHorner.subst_qzero]
      using zero_margin_at f (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift N) zero hh
  exact GaussianGammaNegativeIntervalNamedComparisonTransfer.order_from_zero _ _ _ _
    (name_regular fractionLocationF N (mesh N) N (root_source N)) (name_regular f x E N hs)
    (order_with_margin f x E N zero qzero hs usable)

theorem actual_named_negative_Gamma_log_minimum_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) ⟶ realOrder (nameF fractionLocationF) (nameF f)
        (data (var 2) (mesh (var 2)) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (log_minimum f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalNamedMinimum
