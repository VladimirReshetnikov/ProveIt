import IPRADerivations.Analysis.Stirling.Binet.Bose.ImproperNames.GaussianBinetBoseHorizonRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateComposition
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# The actual improper second Binet integral

Each observation samples the fixed-horizon integral at a computed
positive upper limit. That fixed-horizon sampler uses its own original
positive compact quadrature at a dyadic initial endpoint.
-/

set_option autoImplicit false
set_option maxHeartbeats 560000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseImproperName

open_ipra
open GaussianBinetBoseHorizonRate (ordered_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName
  (sampleData field0 field1 field2 field3 field4)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate rate_at denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "CompactF" => GaussianBinetBoseOriginName.nameF
local notation "compactData" => GaussianBinetBoseOriginName.data
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def source (X _Y D sign K : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source X D sign ⋏ le D (K*X)

ipra_subst source [GaussianRightHalfPlaneLogarithm.source, GaussianRightHalfPlaneArgument.source]

def schedule (p K : PTm n) : PTm n := one+(two*K)*unit (succ p)

def data (X Y D sign K : PTm n) : PTm n := sampleData X Y D sign K zero

def sample (p X Y D sign K : PTm n) : PTm n :=
  ap2 CompactF (succ p) (compactData X Y D sign (schedule p K))

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) : PTm 2)

ipra_subst schedule [one, two]

ipra_subst data

ipra_subst sample

theorem sample_at (p X Y D sign K : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data X Y D sign K) ≐ sample p X Y D sign K := by
  convert GaussianCompactRiemannName.packed_observation_at (Γ := Γ)
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 7) p X Y D sign K zero using 2 <;>
    simp only [nameF, data, subst_sample, Syn.subst_var] <;> rfl

theorem schedule_positive (p K : PTm n) : Γ ⊢[PRAAx] le one (schedule p K) := le_add_right _ _

theorem schedule_monotone (p q K : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (schedule p K) (schedule q K) :=
  add_le_add₂ (le_refl one) (le_mul_mono (le_refl (two*K))
    (GaussianExponentialReference.unit_monotone (le_congr (succ_eq_add_one p).eqSymm (succ_eq_add_one q).eqSymm
      (add_le_add_right one h))))

theorem schedule_budget (p K : PTm n) : Γ ⊢[PRAAx] le ((two*K)*unit (succ p)) (schedule p K) :=
  le_add_left _ _

theorem canonical_source (X Y D sign : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign) :
    Γ ⊢[PRAAx] source X Y D sign D :=
  .andI hz (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl D) hz.andE₁.andE₁))

theorem sample_canonical (p X Y D sign K : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p (data X Y D sign K)) :=
  GaussianRationalHorner.canonical_congr (sample_at p X Y D sign K)
    (GaussianBinetBoseOriginName.sample_canonical (succ p) X Y D sign (schedule p K))

/-- Each actual improper observation agrees with sufficiently late
fixed-horizon observations up to their independent dyadic allowances. -/
theorem late_observations (p q X Y D sign K L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) (hL : Γ ⊢[PRAAx] le (schedule p K) L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign K)) (ap2 CompactF q (compactData X Y D sign L))
      (unit p+unit q) (unit p*unit q) := by
  let C := schedule p K
  let N := C
  let W := unit (succ p)
  let a := compactData X Y D sign C
  let b := compactData X Y D sign L
  have hN : Γ ⊢[PRAAx] le one N := schedule_positive p K
  have hb : Γ ⊢[PRAAx] le ((two*K)*W) N := schedule_budget p K
  have original := rate_at CompactF CompactF a b (two*K) N (succ p) q
    (ordered_rate X Y D sign K C L h.andE₁ h.andE₂ hN hL)
  exact distance_congr (sample_at p X Y D sign K).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedRateRadius.distance_at_first_succ _ _ (two*K) N p q hN hb original)

theorem observations (p q X Y D sign K : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign K) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign K)) (ap2 nameF q (data X Y D sign K))
      (unit p+unit q) (unit p*unit q) := by
  refine (le_total (schedule p K) (schedule q K)).orE ?_ ?_
  · exact GaussianNamedRateRadius.relax_second_clock _ _ p q (succ q) (le_succ_self q)
      (distance_congr (.eqRefl _) (sample_at q X Y D sign K).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations p (succ q) X Y D sign K (schedule q K) h.wk Prf.hyp0))
  · have raw := GaussianNamedRateRadius.relax_second_clock _ _ q p (succ p) (le_succ_self p)
      (distance_congr (.eqRefl _) (sample_at p X Y D sign K).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations q (succ p) X Y D sign K (schedule p K) h.wk Prf.hyp0))
    exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) raw)

theorem regular (X Y D sign K : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign K) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign K) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s K) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Δ,s,Syn.shift,subst_data] using
    observations (var 1) (var 0) (s X) (s Y) (s D) (s sign) (s K) hs

private theorem prefix_diagonal (p X Y D sign K L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign K))
      (ap2 CompactF p (compactData X Y D sign L))
      (diagonalNumerator (two*K) L two p) (diagonalDenominator L p) := by
  let C := schedule p K
  let U := unit p
  let W := unit (succ p)
  let N := L
  have hu := unit_positive (Γ := Γ) p
  have hN : Γ ⊢[PRAAx] le one N := hL
  have hNU := positive_product _ _ hN hu
  refine (le_total L C).orE ?_ ?_
  · have raw := rate_at CompactF CompactF (compactData X Y D sign L) (compactData X Y D sign C) (two*K) N p (succ p)
      (ordered_rate X Y D sign K L C h.andE₁.wk h.andE₂.wk hL.wk Prf.hyp0)
    have den := denominator_positive N p (succ p) hN
    apply distance_congr (sample_at p X Y D sign K).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    apply distance_radius_mono _ _ _ _ _ _ den.wk hNU.wk ?_ (distance_symmetric _ _ _ _ den.wk raw)
    have grow : le L C :: Γ ⊢[PRAAx] le U W := GaussianExponentialReference.unit_monotone (le_succ_self p)
    change (le L C :: Γ) ⊢[PRAAx] le (((two*K)*U*W+N*(U+W))*(N*U)) (((two*K)*U+two*N)*(N*U*W))
    ipra_le 𝔞(N)*𝔞(N)*𝔞(U)*sl grow
  · apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu.wk hu.wk) hNU.wk ?_
      (late_observations p p X Y D sign K L h.wk Prf.hyp0)
    refine le_of_eq_add (d := (two*K)*U*U*U) ?_
    dsimp only [diagonalNumerator,diagonalDenominator,U,N]
    ipra_ring

/-- The improper name and the actual name at any positive integer horizon
`L` differ by at most `2 K/L` plus the observation allowances. -/
theorem prefix_rate (X Y D sign K L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] independentRate nameF CompactF (data X Y D sign K) (compactData X Y D sign L)
      (two*K) L := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two
    hL
    (regular X Y D sign K h) (GaussianBinetBoseOriginName.regular X Y D sign L (.andI h.andE₁ hL))
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s K) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  have hl : Δ ⊢[PRAAx] le one (s L) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hL.shift
  simpa only [diagonalEnvelope,Syn.shift,s,subst_data,GaussianBinetBoseOriginName.subst_data,PTm.subst_mul,
    two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    prefix_diagonal (var 0) (s X) (s Y) (s D) (s sign) (s K) (s L) hs hl

/-- A direct bound against the original positive compact sampler at any
dyadic starting time and positive integer upper horizon. -/
theorem compact_rate (X Y D sign K T L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign K) (ht : Γ ⊢[PRAAx] le one T) :
    Γ ⊢[PRAAx] independentRate nameF GaussianBinetBoseCompact.nameF (data X Y D sign K)
      (GaussianBinetBoseOriginExhaustion.cutData X Y D sign T L)
      ((two*K)*(GaussianBinetBoseOriginExhaustion.cutoff L*(num 4*X))+D*T)
      (T*(GaussianBinetBoseOriginExhaustion.cutoff L*(num 4*X))) :=
  GaussianNamedRateComposition.compose nameF CompactF GaussianBinetBoseCompact.nameF
    (data X Y D sign K) (compactData X Y D sign T) (GaussianBinetBoseOriginExhaustion.cutData X Y D sign T L)
    (two*K) T D (GaussianBinetBoseOriginExhaustion.cutoff L*(num 4*X)) ht
    (positive_product _ _ (GaussianBinetBoseOriginExhaustion.cutoff_positive L)
      (positive_product _ _ (by ipra_le 3) h.andE₁.andE₁.andE₁))
    (prefix_rate X Y D sign K T h ht)
    (GaussianBinetBoseOriginName.prefix_rate X Y D sign T L (.andI h.andE₁ ht))

theorem actual_second_Binet_improper_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0))

theorem actual_second_Binet_improper_horizon_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶ independentRate nameF CompactF
      (data (var 0) (var 1) (var 2) (var 3) (var 4))
      (compactData (var 0) (var 1) (var 2) (var 3) (var 5)) (two*var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (prefix_rate _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseImproperName
