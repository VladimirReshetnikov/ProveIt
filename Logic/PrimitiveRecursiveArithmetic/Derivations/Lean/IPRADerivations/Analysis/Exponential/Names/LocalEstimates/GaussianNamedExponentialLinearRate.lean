import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# Quadratic linearization of the original exponential of a small name

A uniform rational norm bound on the original canonical samples gives
the quadratic error for the actual exponential name and the actual
name for one plus its argument. Both observation clocks are independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianNamedExponentialLinearRate

open_ipra
open GaussianBalancedRadiusArithmetic (unit_monotone)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast sum_distance)
open GaussianNameEquivalence (point_at)
open GaussianNameRingLaws (oneF one_at one_fast add_sample_error three)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRadiusExponentialName (nameF name_regular data sample_at inputPrecision index query)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical positive_product qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qadd_congr)
open GaussianReconstructionRoots (distance_triangle)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def smallSamples (f : PR 2) (x A B : PTm n) : Fm PTm n :=
  .all (bounded (ap2 f (var 0) (Syn.shift x)) (Syn.shift A) (Syn.shift B) ⋏
    canonical (ap2 f (var 0) (Syn.shift x)))

def source (f : PR 2) (x A B : PTm n) : Fm PTm n :=
  le one B ⋏ (le A B ⋏ (pointCN f x ⋏ smallSamples f x A B))

def linearF (f : PR 2) : PR 2 := addF oneF f
def linearData (x : PTm n) : PTm n := addData zero x

ipra_subst smallSamples [Syn.subst_shift, Syn.shift_subst]

ipra_subst source [one]

ipra_subst linearData

theorem sample_input (f : PR 2) (x A B p : PTm n) (hs : Γ ⊢[PRAAx] smallSamples f x A B) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) A B ⋏ canonical (ap2 f p x) := by
  simpa [smallSamples] using hs.allE p

theorem unit_input (f : PR 2) (x A B : PTm n) (h : Γ ⊢[PRAAx] source f x A B) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input f one x := by
  refine .andI h.andE₂.andE₂.andE₁ (.allI ?_)
  let Δ := Γ.map Fm.shift
  let s (t : PTm n) := Syn.shift t
  have hs : Δ ⊢[PRAAx] source f (s x) (s A) (s B) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  have b := (sample_input f (s x) (s A) (s B) (var 0) hs.andE₂.andE₂.andE₂).andE₁
  have r : Δ ⊢[PRAAx] bounded (ap2 f (var 0) (s x)) one one :=
    bounded_radius_mono _ _ _ one one hs.andE₁ (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) hs.andE₂.andE₁) b
  simpa only [GaussianRadiusExponentialName.boundedSamples, Δ, s, Syn.shift, one,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using r

private theorem radius_one_index (p : PTm n) : Γ ⊢[PRAAx] le one (index one p) := by
  have floor : Γ ⊢[PRAAx] le two (GaussianRationalExponentialTail.cutoff one (p+num 4)) := by
    unfold GaussianRationalExponentialTail.cutoff ExponentialTail.Nt
    ipra_le 𝔞(p)+10
  exact (succ_monus_succ one (index one p)).eqSymm.eqTrans
    (le_congr (.eqRefl _) (GaussianRationalExponentialTail.last_successor one (p+num 4)).eqSymm floor)

private theorem query_close (f : PR 2) (x p : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] distanceBounded (query f one p x) (ap2 f p x) two (unit p) := by
  let q := inputPrecision one p
  let U := unit p
  let V := unit q
  have hp : Γ ⊢[PRAAx] le p q := le_trans (le_add_right _ _) (le_add_right _ _)
  have hUV : Γ ⊢[PRAAx] le U V := unit_monotone p q hp
  have hU := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive q) hU) hU
    (by ipra_le 𝔞(U)*sl hUV) (point_at f x q p h)

theorem diagonal (f : PR 2) (x A B p : PTm n) (h : Γ ⊢[PRAAx] source f x A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data one x)) (ap2 (linearF f) p (linearData x))
      (diagonalNumerator (A*A) (B*B) (num 5) p) (diagonalDenominator (B*B) p) := by
  let u := query f one p x
  let v := ap2 f p x
  let U := unit p
  let D := B*B
  let hf := h.andE₂.andE₂.andE₁
  have hB := h.andE₁
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ hB hB
  have hU := unit_positive (Γ := Γ) p
  have hquery := sample_input f x A B (inputPrecision one p) h.andE₂.andE₂.andE₂
  have finite := GaussianExponentialLinearRemainder.original_finite_linear_remainder u A B (index one p)
    hB h.andE₂.andE₁ hquery.andE₁ hquery.andE₂ (radius_one_index p)
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data one x)) (qadd qone u) (A*A) D :=
    distance_congr (sample_at f one p x).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) finite
  have shift : Γ ⊢[PRAAx] distanceBounded (qadd qone u) (qadd qone v) two U :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (sum_distance qone qone u v zero two U hU (distance_refl_zero _ _ hU) (query_close f x p hf))
  have add := distance_congr (.eqRefl _) (qadd_congr (one_at p zero) (.eqRefl v)) (.eqRefl _) (.eqRefl _)
    (add_sample_error oneF f zero x p (one_fast zero) hf)
  have last : Γ ⊢[PRAAx] distanceBounded (qadd qone u) (ap2 (linearF f) p (linearData x)) (num 5) U := by
    have joined := distance_triangle_same _ _ _ two three U hU shift (distance_symmetric _ _ _ _ hU add)
    exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _) joined
  exact distance_triangle _ _ _ (A*A) D (num 5) U hD hU first last

theorem independent_rate (f : PR 2) (x A B : PTm n) (h : Γ ⊢[PRAAx] source f x A B) :
    Γ ⊢[PRAAx] independentRate (nameF f) (linearF f) (data one x) (linearData x) (A*A) (B*B) := by
  apply GaussianNamedLipschitzRate.independent_rate (nameF f) (linearF f) (data one x) (linearData x)
    (A*A) (B*B) (num 5) (positive_product _ _ h.andE₁ h.andE₁)
    (name_regular f one x (unit_input f x A B h)) (add_fast oneF f _ _ (one_fast zero) h.andE₂.andE₂.andE₁)
  let s (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] source f (s x) (s A) (s B) := by
    simpa only [s,Fm.shift,Syn.shift,subst_source] using h.shift
  refine .allI ?_
  simpa only [diagonalEnvelope, s, Syn.shift, subst_linearData, GaussianRadiusExponentialName.subst_data,
    PTm.subst_mul, PTm.subst_num, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    using diagonal f (s x) (s A) (s B) (var 0) hs

theorem actual_named_exponential_linearization_closed (f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source f (var 0) (var 1) (var 2) ⟶
       independentRate (nameF f) (linearF f) (data one (var 0)) (linearData (var 0))
         (var 1*var 1) (var 2*var 2)) :=
  closeUniv 3 (.impI (independent_rate f _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedExponentialLinearRate
