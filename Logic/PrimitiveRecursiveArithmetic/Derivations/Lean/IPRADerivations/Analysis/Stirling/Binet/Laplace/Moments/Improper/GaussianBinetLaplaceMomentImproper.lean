import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.FiniteRows.GaussianBinetLaplaceMomentPrefixes
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# The actual improper Binet name for every natural time moment

Read the original weighted compact name at a cofinal integer horizon.
An explicit cutoff pays the inverse-square tail budget at the next
precision. The resulting primitive-recursive name is regular, with a
checked tail rate against every original compact prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentImproper

open_ipra
open GaussianBinetLaplaceMomentPrefixes (prefixData prefix_regular tailNumerator ordered_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent normalizer query_budget)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product canonical)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "StripF" => GaussianBinetLaplaceMomentFloor.nameF

def cutoff (p j D : PTm n) : PTm n := unit (exponent (tailNumerator j D) (succ p))
def data (j X D R : PTm n) : PTm n := sampleData j X D R zero zero
def sample (p j X D R : PTm n) : PTm n := ap2 StripF (succ p) (prefixData j X D R (cutoff p j D))
def nameF : PR 2 := PTm.toPR
  (sample (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) : PTm 2)

ipra_subst cutoff

ipra_subst data

ipra_subst sample

theorem sample_at (p j X D R : PTm n) : Γ ⊢[PRAAx] ap2 nameF p (data j X D R) ≐ sample p j X D R := by
  convert GaussianCompactRiemannName.packed_observation_at (Γ := Γ)
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 7) p j X D R zero zero using 2 <;>
    simp only [nameF, data, subst_sample, Syn.subst_var] <;> rfl

theorem cutoff_positive (p j D : PTm n) : Γ ⊢[PRAAx] le one (cutoff p j D) := unit_positive _

theorem cutoff_monotone (p q j D : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (cutoff p j D) (cutoff q j D) :=
  GaussianExponentialReference.unit_monotone
    (add_le_add_right (normalizer (tailNumerator j D))
      (le_congr (succ_eq_add_one p).eqSymm (succ_eq_add_one q).eqSymm (add_le_add_right one h)))

theorem cutoff_budget (p j D : PTm n) : Γ ⊢[PRAAx] le (tailNumerator j D*unit (succ p)) (cutoff p j D) :=
  query_budget _ _

theorem sample_canonical (p j X D R : PTm n) : Γ ⊢[PRAAx] canonical (ap2 nameF p (data j X D R)) := by
  let T := cutoff p j D
  let F := GaussianBinetLaplaceMomentFloor.evaluatorF
  have hs : Γ ⊢[PRAAx] canonical (sample p j X D R) :=
    GaussianCompactRiemannName.name_canonical F (succ p) (one+zero) T one
      (GaussianBinetLaplaceMomentFloor.gain j R T) T (GaussianBinetLaplaceMomentFloor.fixedData j X D R T)
  exact GaussianRationalHorner.canonical_congr (sample_at p j X D R) hs

theorem late_observations (p q j X D R L : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hL : Γ ⊢[PRAAx] le (cutoff p j D) L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R)) (ap2 StripF q (prefixData j X D R L))
      (unit p+unit q) (unit p*unit q) := by
  let C := cutoff p j D
  let N := tailNumerator j D
  let a := prefixData j X D R C
  let b := prefixData j X D R L
  have hC := cutoff_positive (Γ := Γ) p j D
  have hb := cutoff_budget (Γ := Γ) p j D
  have original := rate_at StripF StripF a b N C (succ p) q (ordered_rate j X D R C L h hC hL)
  exact distance_congr (sample_at p j X D R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedRateRadius.distance_at_first_succ _ _ N C p q hC hb original)

theorem observations (p q j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R)) (ap2 nameF q (data j X D R))
      (unit p+unit q) (unit p*unit q) := by
  exact GaussianNamedRateRadius.ordered_cutoff_observations p q (cutoff p j D) (cutoff q j D)
    (sample_at p j X D R) (sample_at q j X D R)
    (late_observations p (succ q) j X D R (cutoff q j D) h.wk Prf.hyp0)
    (late_observations q (succ p) j X D R (cutoff p j D) h.wk Prf.hyp0)

theorem regular (j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] pointCN nameF (data j X D R) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Δ,s,Syn.shift,subst_data] using
    observations (var 1) (var 0) (s j) (s X) (s D) (s R) hs

private theorem prefix_diagonal (p j X D R L : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R)) (ap2 StripF p (prefixData j X D R L))
      (diagonalNumerator (tailNumerator j D) L two p) (diagonalDenominator L p) := by
  let C := cutoff p j D
  exact GaussianNamedLipschitzRate.ordered_prefix_diagonal StripF p (tailNumerator j D) L L C
    (prefixData j X D R L) (prefixData j X D R C) hL (sample_at p j X D R)
    (ordered_rate j X D R L C h.wk hL.wk Prf.hyp0)
    (late_observations p p j X D R L h.wk Prf.hyp0)

theorem prefix_rate (j X D R L : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] independentRate nameF StripF (data j X D R) (prefixData j X D R L) (tailNumerator j D) L := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two hL
    (regular j X D R h) (prefix_regular j X D R L h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift
  have hl : Δ ⊢[PRAAx] le one (s L) := Order.shift_one_le hL
  simpa only [diagonalEnvelope,Syn.shift,s,subst_data,GaussianBinetLaplaceMomentPrefixes.subst_prefixData,
    GaussianBinetLaplaceMomentPrefixes.subst_tailNumerator,two,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using prefix_diagonal (var 0) (s j) (s X) (s D) (s R) (s L) hs hl

theorem actual_weighted_Binet_improper_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (realSource (var 1) zero (var 2) zero (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

theorem actual_weighted_Binet_improper_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (realSource (var 1) zero (var 2) zero (var 3) ⟶ le one (var 4) ⟶
      independentRate nameF StripF (data (var 0) (var 1) (var 2) (var 3))
        (prefixData (var 0) (var 1) (var 2) (var 3) (var 4)) (tailNumerator (var 0) (var 2)) (var 4)) :=
  closeUniv 5 (.impI (.impI (prefix_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentImproper
