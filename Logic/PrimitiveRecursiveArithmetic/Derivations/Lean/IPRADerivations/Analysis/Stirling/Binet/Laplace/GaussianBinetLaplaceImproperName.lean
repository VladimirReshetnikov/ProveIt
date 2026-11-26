import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceOrderedPrefixes
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# The actual cofinal Binet Laplace name

Each sample reads the original compact integral on `[0,D*L]`, where
the dyadic budget of the cutoff `L` absorbs the improper-integral tail.
The original finite prefixes retain their independent cutoff comparison.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceImproperName

open_ipra
open GaussianBinetLaplaceOrderedPrefixes (prefixData subst_prefixData prefix_regular ordered_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleData field0 field1 field2 field3 field4)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (exponent normalizer query_budget)
open GaussianLogGammaEulerResidualDomain (source subst_source)
open GaussianNamedInverseRate (independentRate rate_at denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "StripF" => GaussianBinetLaplaceStrip.nameF GaussianBinetLaplaceStrip.Kernel.cofinal
local notation "twelve" => num 12
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def cutoff (p D : PTm n) : PTm n := exponent D (succ p)

def data (X Y D sign R : PTm n) : PTm n := sampleData X Y D sign R zero

def sample (p X Y D sign R : PTm n) : PTm n :=
  ap2 StripF (succ p) (prefixData X Y D sign R (cutoff p D))

def nameF : PR 2 := PTm.toPR
  (sample (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) : PTm 2)

ipra_subst cutoff

ipra_subst data

ipra_subst sample

theorem sample_at (p X Y D sign R : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data X Y D sign R) ≐ sample p X Y D sign R := by
  convert GaussianCompactRiemannName.packed_observation_at (Γ := Γ)
    (sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 7) p X Y D sign R zero using 2 <;>
    simp only [nameF, data, subst_sample, Syn.subst_var] <;> rfl

theorem cutoff_positive (p D : PTm n) : Γ ⊢[PRAAx] le one (cutoff p D) :=
  le_trans (zero_lt_succ p) (le_add_right (succ p) (normalizer D))

theorem cutoff_monotone (p q D : PTm n) (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] le (cutoff p D) (cutoff q D) :=
  add_le_add_right (normalizer D)
    (le_congr (succ_eq_add_one p).eqSymm (succ_eq_add_one q).eqSymm (add_le_add_right one h))

private theorem prefix_denominator_positive (X L : PTm n) (hX : Γ ⊢[PRAAx] le one X) :
    Γ ⊢[PRAAx] le one (twelve*X*unit L) :=
  positive_product _ _ (positive_product _ _ (by ipra_le 11) hX) (unit_positive L)

theorem sample_canonical (p X Y D sign R : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalHorner.canonical (ap2 nameF p (data X Y D sign R)) := by
  let T := D*cutoff p D*one
  have hs : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (sample p X Y D sign R) :=
    GaussianCompactRiemannName.name_canonical (GaussianBinetLaplaceStrip.evaluatorF .cofinal)
      (succ p) (one+zero) T one (GaussianBinetLaplaceIntegrand.meshGain R T) T
      (GaussianBinetLaplaceStrip.fixedData X Y D sign R T zero)
  exact GaussianRationalHorner.canonical_congr (sample_at p X Y D sign R) hs

/-- Each actual improper observation is already within its usual dyadic
allowance of any late compact prefix, in addition to the prefix's own
observation allowance. -/
theorem late_observations (p q X Y D sign R L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hL : Γ ⊢[PRAAx] le (cutoff p D) L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign R)) (ap2 StripF q (prefixData X Y D sign R L))
      (unit p+unit q) (unit p*unit q) := by
  let C := cutoff p D
  let N := twelve*X*unit C
  let W := unit (succ p)
  let a := prefixData X Y D sign R C
  let b := prefixData X Y D sign R L
  have hX := h.andE₁.andE₁.andE₁
  have hN : Γ ⊢[PRAAx] le one N := prefix_denominator_positive X C hX
  have hb : Γ ⊢[PRAAx] le (D*W) N := by
    have twelveX : Γ ⊢[PRAAx] le one (twelve*X) := positive_product _ _ (by ipra_le 11) hX
    exact le_trans (query_budget D (succ p))
      (le_congr (by ipra_ring : Γ ⊢[PRAAx] one*unit C ≐ unit C) (.eqRefl N) (mul_le_mul_right (unit C) twelveX))
  have original := rate_at StripF StripF a b D N (succ p) q
    (ordered_rate X Y D sign R C L h (cutoff_positive p D) hL)
  exact distance_congr (sample_at p X Y D sign R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (GaussianNamedRateRadius.distance_at_first_succ _ _ D N p q hN hb original)

theorem observations (p q X Y D sign R : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign R)) (ap2 nameF q (data X Y D sign R))
      (unit p+unit q) (unit p*unit q) := by
  refine (le_total (cutoff p D) (cutoff q D)).orE ?_ ?_
  · exact GaussianNamedRateRadius.relax_second_clock _ _ p q (succ q) (le_succ_self q)
      (distance_congr (.eqRefl _) (sample_at q X Y D sign R).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations p (succ q) X Y D sign R (cutoff q D) h.wk Prf.hyp0))
  · have raw := GaussianNamedRateRadius.relax_second_clock _ _ q p (succ p) (le_succ_self p)
      (distance_congr (.eqRefl _) (sample_at p X Y D sign R).eqSymm (.eqRefl _) (.eqRefl _)
        (late_observations q (succ p) X Y D sign R (cutoff p D) h.wk Prf.hyp0))
    exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive p)) raw)

theorem regular (X Y D sign R : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] pointCN nameF (data X Y D sign R) := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,unit,Δ,s,Syn.shift,subst_data] using
    observations (var 1) (var 0) (s X) (s Y) (s D) (s sign) (s R) hs

private theorem prefix_diagonal (p X Y D sign R L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data X Y D sign R))
      (ap2 StripF p (prefixData X Y D sign R L))
      (diagonalNumerator D (twelve*X*unit L) two p) (diagonalDenominator (twelve*X*unit L) p) := by
  let C := cutoff p D
  let U := unit p
  let W := unit (succ p)
  let N := twelve*X*unit L
  have hu := unit_positive (Γ := Γ) p
  have hN : Γ ⊢[PRAAx] le one N := prefix_denominator_positive X L h.andE₁.andE₁.andE₁
  have hNU := positive_product _ _ hN hu
  refine (le_total L C).orE ?_ ?_
  · have raw := rate_at StripF StripF (prefixData X Y D sign R L) (prefixData X Y D sign R C) D N p (succ p)
      (ordered_rate X Y D sign R L C h.wk hL.wk Prf.hyp0)
    have den := denominator_positive N p (succ p) hN
    apply distance_congr (sample_at p X Y D sign R).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    apply distance_radius_mono _ _ _ _ _ _ den.wk hNU.wk ?_ (distance_symmetric _ _ _ _ den.wk raw)
    have grow : le L C :: Γ ⊢[PRAAx] le U W := GaussianExponentialReference.unit_monotone (le_succ_self p)
    change (le L C :: Γ) ⊢[PRAAx] le ((D*U*W+N*(U+W))*(N*U)) ((D*U+two*N)*(N*U*W))
    ipra_le 𝔞(N)*𝔞(N)*𝔞(U)*sl grow
  · apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hu.wk hu.wk) hNU.wk ?_
      (late_observations p p X Y D sign R L h.wk Prf.hyp0)
    refine le_of_eq_add (d := D*U*U*U) ?_
    dsimp only [diagonalNumerator,diagonalDenominator,U,N]
    ipra_ring

/-- The cofinal improper name and any actual compact prefix differ by at
most `D/(12 X 2^L)` plus the two independent observation allowances. -/
theorem prefix_rate (X Y D sign R L : PTm n)
    (h : Γ ⊢[PRAAx] source X Y D sign R) (hL : Γ ⊢[PRAAx] le one L) :
    Γ ⊢[PRAAx] independentRate nameF StripF (data X Y D sign R) (prefixData X Y D sign R L)
      D (twelve*X*unit L) := by
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ two
    (prefix_denominator_positive X L h.andE₁.andE₁.andE₁)
    (regular X Y D sign R h) (prefix_regular X Y D sign R L h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  have hl : Δ ⊢[PRAAx] le one (s L) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hL.shift
  simpa only [diagonalEnvelope,Syn.shift,s,subst_data,subst_prefixData,
    GaussianCoefficientNameBounds.subst_unit,PTm.subst_mul,PTm.subst_num,two,one,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using prefix_diagonal (var 0) (s X) (s Y) (s D) (s sign) (s R) (s L) hs hl

theorem actual_Binet_Laplace_improper_name_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (regular _ _ _ _ _ Prf.hyp0))

theorem actual_Binet_Laplace_improper_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ le one (var 5) ⟶
      independentRate nameF StripF (data (var 0) (var 1) (var 2) (var 3) (var 4))
        (prefixData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) (var 2) (twelve*var 0*unit (var 5))) :=
  closeUniv 6 (.impI (.impI (prefix_rate _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceImproperName
