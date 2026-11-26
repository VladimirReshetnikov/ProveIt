import IPRADerivations.Analysis.Gamma.Digamma.PositiveNames.GaussianGammaPositiveNamedDigammaRecurrenceInput
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaRecurrence
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDiagonalRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# Positive named digamma recurrence

The value at the original named input plus one equals the original
normalized Gamma derivative plus the actual certified reciprocal of
the input. The two digamma freezes and the reciprocal freeze share the
exact rational observation used by the shift sampler.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaRecurrence

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerNamedShiftInput (shiftF shiftData clock_later)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianGammaMinimumFreezeRational (numerator denominator frozen_rational_domain)
open GaussianGammaPositiveNamedDigammaFrozen (frozenData gain original_rate)
open GaussianGammaPositiveNamedDigammaRecurrenceInput
  (shifted_source shifted_fraction native_fraction_proper reciprocal_input frozen_reciprocal)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameReciprocal (anchor modulus)
open GaussianNamedPositiveDigamma (source nameF data name_regular)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNamedRightHalfPlane (threshold)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "N" => GaussianGammaDigammaNative.nameF
local notation "S" => GaussianGammaDigammaRecurrence.nameF
local notation "R" => GaussianNameReciprocal.nameF
local notation "c" => GaussianGammaPositiveNamedRationalFreeze.clock

def sumF (f : PR 2) : PR 2 := addF (nameF f) (R f)
def sumData (f : PR 2) (x A : PTm n) : PTm n :=
  addData (data f x A) (GaussianNameReciprocal.nameData (threshold A) x)

def shiftedClock (f : PR 2) (p x A : PTm n) : PTm n :=
  p+c (shiftF f) p one (shiftData x) A+c f p one x A+anchor (threshold A)

def cost (f : PR 2) (x A : PTm n) : PTm n :=
  gain (shiftF f) (shiftData x) A + (gain f x A+modulus (threshold A))

ipra_subst sumData

ipra_subst cost

theorem sum_regular (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] pointCN (sumF f) (sumData f x A) := by
  have i := reciprocal_input f x A h
  exact add_fast _ _ _ _ (name_regular f x A h)
    (GaussianNameReciprocal.name_fast f (threshold A) x i.andE₁ i.andE₂)

private theorem reciprocal_rate (f : PR 2) (p k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hp : Γ ⊢[PRAAx] le p k) (hk : Γ ⊢[PRAAx] le (anchor (threshold A)) k) :
    Γ ⊢[PRAAx] independentRate (R f) constantF (GaussianNameReciprocal.nameData (threshold A) x)
      (fraction (denominator f k x) (numerator f k x)) (modulus (threshold A)) (unit p) := by
  let M := modulus (threshold A)
  let u := GaussianNameReciprocal.nameData (threshold A) x
  let v := GaussianNamedReciprocalFrozenRate.frozen f x k
  let w := fraction (denominator f k x) (numerator f k x)
  have hi := reciprocal_input f x A h
  have ir := GaussianNameReciprocal.name_fast f (threshold A) x hi.andE₁ hi.andE₂
  have raw := GaussianNamedReciprocalFrozenRate.frozen_rate f (threshold A) x k hi hk
  have rate := GaussianNamedRateRadius.weaken_dyadic (R f) constantF u v M p k hp raw
  have e := cross_data_congr constantF constantF v w v v (frozen_reciprocal f k x A h hk) (.eqRefl v)
    (cross_refl _ _ (constant_regular v))
  exact GaussianNamedRateTransport.transport (R f) constantF (R f) constantF u v u w M (unit p)
    (unit_positive p) rate (cross_refl _ _ ir) e

private theorem sum_rate (f : PR 2) (p k x A : PTm n) (h : Γ ⊢[PRAAx] source f x A)
    (hp : Γ ⊢[PRAAx] le p k) (hk : Γ ⊢[PRAAx] le (c f p one x A) k)
    (ha : Γ ⊢[PRAAx] le (anchor (threshold A)) k) :
    Γ ⊢[PRAAx] independentRate (sumF f) S (sumData f x A)
      (GaussianGammaDigammaRecurrence.data (numerator f k x) (denominator f k x))
      (gain f x A+modulus (threshold A)) (unit p) := by
  let D := gain f x A
  let M := modulus (threshold A)
  let u := data f x A
  let v := GaussianNameReciprocal.nameData (threshold A) x
  let y := frozenData f k x
  let z := fraction (denominator f k x) (numerator f k x)
  let U := unit p
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have both := GaussianNamedAddRate.independent_rate (nameF f) (R f) N constantF u v y z D U M U hU hU
    (original_rate f p k x A h hk) (reciprocal_rate f p k x A h hp ha)
  exact GaussianNamedRateRadius.weaken (sumF f) S (sumData f x A) (addData y z) _ _ (D+M) U
    (positive_product _ _ hU hU) hU
    (le_of_eq_add (d := zero) (by unfold GaussianNamedRateComposition.leadingNumerator; ipra_ring))
    both

theorem comparison_rate (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] independentRate (nameF (shiftF f)) (sumF f) (data (shiftF f) (shiftData x) A)
      (sumData f x A) (cost f x A) (unit p) := by
  let g := shiftF f
  let y := shiftData x
  let k := shiftedClock f p x A
  let l := GaussianEulerNamedShiftInput.clock k
  let a := numerator f l x
  let b := denominator f l x
  let u := data g y A
  let v := frozenData g k y
  let w := GaussianGammaDigammaRecurrence.data a b
  let U := unit p
  let C := gain g y A
  let D := gain f x A+modulus (threshold A)
  have hg := shifted_source f x A h
  have hk : Γ ⊢[PRAAx] le (c g p one y A) k :=
    le_trans (le_add_left _ p) (le_trans (le_add_right _ _) (le_add_right _ _))
  have hl : Γ ⊢[PRAAx] le (c f p one x A) l :=
    le_trans (le_add_left _ _) (le_trans (le_add_right _ _) (clock_later k))
  have hp : Γ ⊢[PRAAx] le p l :=
    le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (le_trans (le_add_right _ _) (clock_later k)))
  have ha : Γ ⊢[PRAAx] le (anchor (threshold A)) l :=
    le_trans (le_add_left _ _) (clock_later k)
  have t := le_trans (GaussianGammaPositiveNamedRationalFreeze.threshold_le g p one y A) hk
  have hs := (frozen_rational_domain g k y A hg t).andE₁
  have hb := (frozen_rational_domain f l x A h (le_trans t (clock_later k))).andE₁
  have equiv := native_fraction_proper _ _ (a+b) b hs
    (GaussianStirlingGammaLogarithm.source_shift a b hb) (shifted_fraction f k x A h t)
  have native := cross_trans _ _ _ _ _ _ equiv (GaussianGammaDigammaRecurrence.digamma_shift a b hb)
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have gRate := original_rate g p k y A hg hk
  have left := GaussianNamedRateTransport.transport (nameF g) N (nameF g) S u v u w C U hU gRate
    (cross_refl _ _ (name_regular g y A hg)) (cross_symm _ _ _ _ native)
  have right := GaussianNamedRateComposition.symmetric (sumF f) S (sumData f x A) w D U hU
    (sum_rate f p l x A h hp hl ha)
  exact GaussianNamedRateComposition.same_denominator (nameF g) S (sumF f) u w (sumData f x A)
    C U D hU left right

private theorem observation_bound (f : PR 2) (p x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF (shiftF f)) p (data (shiftF f) (shiftData x) A))
      (ap2 (sumF f) p (sumData f x A)) (cost f x A+two) (unit p) := by
  have pos := unit_positive (Γ := Γ) p
  exact GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ (positive_product _ _ pos pos) pos
    (le_of_eq_add (d := zero) (by ipra_ring))
    (diagonal_rate _ _ _ _ (cost f x A) (unit p) p pos (comparison_rate f p x A h))

theorem recurrence (f : PR 2) (x A : PTm n) (h : Γ ⊢[PRAAx] source f x A) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (shiftF f)) (sumF f)
      (data (shiftF f) (shiftData x) A) (sumData f x A) := by
  apply GaussianNamedDiagonalRate.cross_of_diagonal_rate _ _ _ _ (cost f x A+two)
    (name_regular _ _ _ (shifted_source f x A h)) (sum_regular f x A h)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (Syn.shift x) (Syn.shift A) :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI ?_
  simpa only [GaussianNamedDiagonalRate.diagonalRate,Syn.shift,GaussianNamedPositiveDigamma.subst_data,
    GaussianEulerNamedShiftInput.subst_shiftData,subst_sumData,subst_cost,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observation_bound f (var 0) (Syn.shift x) (Syn.shift A) hs

theorem actual_original_positive_named_digamma_recurrence_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (source f (var 0) (var 1) ⟶ crossEquivalent (nameF (shiftF f)) (sumF f)
        (data (shiftF f) (shiftData (var 0)) (var 1)) (sumData f (var 0) (var 1))) :=
  closeUniv 2 (.impI (recurrence f _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaPositiveNamedDigammaRecurrence
