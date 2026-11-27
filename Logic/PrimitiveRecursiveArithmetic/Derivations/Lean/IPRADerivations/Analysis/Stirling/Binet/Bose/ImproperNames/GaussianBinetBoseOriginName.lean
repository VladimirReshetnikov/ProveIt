import IPRADerivations.Analysis.Stirling.Binet.Bose.ImproperNames.GaussianBinetBoseOriginExhaustion
import IPRADerivations.Analysis.Names.Order.GaussianFastValueCut
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius

/-!
# The original Bose integral including the origin at a fixed horizon

Actual observations use the original positive compact integral with
a dyadic initial endpoint chosen from the requested accuracy.
-/

set_option autoImplicit false
set_option maxHeartbeats 540000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseOriginName

open_ipra
open GaussianBinetBoseCompact (evaluatorF gain)
open GaussianBinetBoseOriginExhaustion (cutData subst_cutData cut_regular ordered_rate width)
open GaussianCoefficientNameBounds (unit)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent normalizer query_budget)
open GaussianNamedInverseRate (independentRate rate_at)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "CompactF" => GaussianBinetBoseCompact.nameF
local notation "panelDen" => GaussianBinetBoseOriginExhaustion.cutoff

def source (X _Y D sign T : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source X D sign ⋏ le one T

ipra_subst source [GaussianRightHalfPlaneLogarithm.source, GaussianRightHalfPlaneArgument.source]

def schedule (p D : PTm n) : PTm n := exponent D (succ p)

def data (X Y D sign T : PTm n) : PTm n := sampleData X Y D sign T zero

def sample (p X Y D sign T : PTm n) : PTm n :=
  ap2 CompactF (succ p) (cutData X Y D sign T (schedule p D))

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) : PTm 2)

ipra_subst schedule

ipra_subst data

ipra_subst sample

theorem sample_at (p X Y D sign T : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data X Y D sign T) ≐ sample p X Y D sign T := by
  convert GaussianCompactRiemannName.packed_observation_at (Γ := Γ)
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 7) p X Y D sign T zero using 2 <;>
    simp only [nameF, data, subst_sample, Syn.subst_var] <;> rfl

theorem schedule_positive (p D : PTm n) : Γ ⊢[PRAAx] le one (schedule p D) :=
  le_trans (zero_lt_succ p) (le_add_right (succ p) (normalizer D))

theorem schedule_monotone (p q D : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (schedule p D) (schedule q D) :=
  add_le_add_right (normalizer D)
    (le_congr (succ_eq_add_one p).eqSymm (succ_eq_add_one q).eqSymm (add_le_add_right one h))

private theorem cutoff_denominator_positive (X L : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le one (panelDen L*(num 4*X)) :=
  positive_product _ _ (GaussianBinetBoseOriginExhaustion.cutoff_positive L)
    (positive_product _ _ (by ipra_le 3) hX)

theorem sample_canonical (p X Y D sign T : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p (data X Y D sign T)) := by
  let L := schedule p D
  let E := panelDen L
  let C := width T L
  have hs : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p X Y D sign T) :=
    GaussianCompactRiemannName.name_canonical evaluatorF (succ p) (E+one) C E (gain D E T) T
      (GaussianBinetArctangentQuadrature.fixedData X Y D sign)
  exact GaussianRationalHorner.canonical_congr (sample_at p X Y D sign T) hs

/-- Each actual observation of the fixed-horizon name agrees with a later
positive compact panel up to their independent dyadic allowances. -/
theorem late_observations (p q X Y D sign T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign T) (hL : Γ ⊢[PRAAx] le (schedule p D) L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign T)) (ap2 CompactF q (cutData X Y D sign T L))
      (unit p+unit q) (unit p*unit q) := by
  let C := schedule p D
  let N := panelDen C*(num 4*X)
  let W := unit (succ p)
  let a := cutData X Y D sign T C
  let b := cutData X Y D sign T L
  have hX := h.andE₁.andE₁.andE₁
  have hN : Γ ⊢[PRAAx] le one N := cutoff_denominator_positive X C hX
  have hb : Γ ⊢[PRAAx] le (D*W) N := by
    have fourX : Γ ⊢[PRAAx] le one (num 4*X) := positive_product _ _ (by ipra_le 3) hX
    have cutoff_later : Γ ⊢[PRAAx] le (unit C) (panelDen C) :=
      GaussianExponentialReference.unit_monotone (le_succ_self C)
    exact le_trans (query_budget D (succ p))
      (le_trans cutoff_later (le_congr (by ipra_ring : Γ ⊢[PRAAx] panelDen C*one ≐ panelDen C) (.eqRefl N) (le_mul_mono (le_refl (panelDen C)) fourX)))
  have original := rate_at CompactF CompactF a b D N (succ p) q
    (ordered_rate X Y D sign T C L h.andE₁ h.andE₂ hL)
  exact distance_congr (sample_at p X Y D sign T).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedRateRadius.distance_at_first_succ _ _ D N p q hN hb original)

theorem observations (p q X Y D sign T : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign T)) (ap2 nameF q (data X Y D sign T))
      (unit p+unit q) (unit p*unit q) := by
  exact GaussianNamedRateRadius.ordered_cutoff_observations p q (schedule p D) (schedule q D)
    (sample_at p X Y D sign T) (sample_at q X Y D sign T)
    (late_observations p (succ q) X Y D sign T (schedule q D) h.wk Prf.hyp0)
    (late_observations q (succ p) X Y D sign T (schedule p D) h.wk Prf.hyp0)

theorem regular (X Y D sign T : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign T) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s T) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Δ,s,Syn.shift,subst_data] using
    observations (var 1) (var 0) (s X) (s Y) (s D) (s sign) (s T) hs

private theorem prefix_diagonal (p X Y D sign T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign T))
      (ap2 CompactF p (cutData X Y D sign T L))
      (diagonalNumerator D (panelDen L*(num 4*X)) two p) (diagonalDenominator (panelDen L*(num 4*X)) p) := by
  let C := schedule p D
  let N := panelDen L*(num 4*X)
  have hN : Γ ⊢[PRAAx] le one N := cutoff_denominator_positive X L h.andE₁.andE₁.andE₁
  exact GaussianNamedLipschitzRate.ordered_prefix_diagonal CompactF p D N L C
    (cutData X Y D sign T L) (cutData X Y D sign T C) hN (sample_at p X Y D sign T)
    (ordered_rate X Y D sign T L C h.andE₁.wk h.andE₂.wk Prf.hyp0)
    (late_observations p p X Y D sign T L h.wk Prf.hyp0)

/-- The fixed-horizon name and any positive compact dyadic panel differ by
at most `D/(4 X 2^(L+1))` plus their independent observation allowances. -/
theorem prefix_rate (X Y D sign T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign T) :
    Γ ⊢[PRAAx] independentRate nameF CompactF (data X Y D sign T) (cutData X Y D sign T L)
      D (panelDen L*(num 4*X)) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two
    (cutoff_denominator_positive X L h.andE₁.andE₁.andE₁)
    (regular X Y D sign T h) (cut_regular X Y D sign T L h.andE₁ h.andE₂)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s T) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  simpa only [diagonalEnvelope,Syn.shift,s,subst_data,subst_cutData,GaussianBinetBoseOriginExhaustion.subst_cutoff,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_num,two,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using prefix_diagonal (var 0) (s X) (s Y) (s D) (s sign) (s T) (s L) hs

theorem actual_second_Binet_fixed_horizon_at_origin_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0))

theorem actual_second_Binet_fixed_horizon_dyadic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ independentRate nameF CompactF
      (data (var 0) (var 1) (var 2) (var 3) (var 4))
      (cutData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (panelDen (var 5)*(num 4*var 0))) :=
  closeUniv 6 (.impI (prefix_rate _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseOriginName
