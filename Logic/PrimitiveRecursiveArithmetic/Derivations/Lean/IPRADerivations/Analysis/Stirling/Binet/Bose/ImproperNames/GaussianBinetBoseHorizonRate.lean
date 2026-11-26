import IPRADerivations.Analysis.Stirling.Binet.Bose.ImproperNames.GaussianBinetBoseOriginName
import IPRADerivations.Analysis.Stirling.Binet.Bose.LiteralTails.GaussianBinetBoseFarQuadrature
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallAddendRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Upper-horizon rate for the actual second Binet integral

At a common positive dyadic start, compact additivity leaves only the
terminal strip. The bound on that strip is uniform in the starting
cutoff. Taking late actual observations preserves the bound after
exhaustion at the origin.
-/

set_option autoImplicit false
set_option maxHeartbeats 630000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseHorizonRate

open_ipra
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBoseCompact (evaluatorF gain)
open GaussianBinetBoseCompactAlignment (additivity data_congr)
open GaussianBinetBoseOriginExhaustion (cutoff cutoff_positive cutData subst_cutData width endpoint panel_source cut_regular)
open GaussianBinetBoseOriginName (schedule late_observations)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedSmallAddendRate (tailSamples)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "F" => GaussianBinetBoseCompact.nameF
local notation "P" => GaussianBinetBoseOriginName.nameF
local notation "panel" => GaussianBinetBoseCompact.data
local notation "origin" => GaussianBinetBoseOriginName.data

theorem tail_samples (X Y D sign U A C E K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBinetBoseCompact.source X D sign U A C E)
    (hC : Γ ⊢[PRAAx] le one C) (hK : Γ ⊢[PRAAx] le D (K*X)) : Γ ⊢[PRAAx]
    tailSamples F (panel X Y D sign U A C E) (two*K*E) A := by
  refine .allI ?_
  let s (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let a := s A
  let w := unit (p+num 6)
  let u := unit p
  let b := two*s K*s E
  have hs : Δ ⊢[PRAAx] GaussianBinetBoseCompact.source (s X) (s D) (s sign) (s U) a (s C) (s E) :=
    by simpa only [Δ,s,a,Fm.shift,Syn.shift,GaussianBinetBoseCompact.subst_source] using h.shift
  have cs : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift
  have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift
  let q := ap2 F p (panel (s X) (s Y) (s D) (s sign) (s U) a (s C) (s E))
  have canon : Δ ⊢[PRAAx] GaussianRationalHorner.canonical q :=
    GaussianCompactRiemannName.name_canonical evaluatorF p (s E+a) (s C) (s E) (gain (s D) (s E) (s U))
      (s U) (fixedData (s X) (s Y) (s D) (s sign))
  have hn := hs.andE₂.andE₁
  have result : Δ ⊢[PRAAx] bounded q (b*u+a) (a*u) := by
    apply GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
      (positive_product _ _ (unit_positive (p+num 6)) hn)
      (positive_product _ _ hn (unit_positive p)) ?_
      (GaussianBinetBoseFarQuadrature.name_bound p (s X) (s Y) (s D) (s sign) (s U) a (s C) (s E) (s K) hs cs ks)
    change Δ ⊢[PRAAx] le ((num 3*a+b*w)*(a*u)) ((b*u+a)*(w*a))
    have grow : Δ ⊢[PRAAx] le (num 3*u) w := GaussianCompactRiemannName.dyadic_six_lower p
    ipra_le 𝔞(a*a)*sl grow
  simpa only [tailSamples,Δ,s,p,q,a,b,u,Syn.shift,GaussianBinetBoseCompact.subst_data,PTm.subst_mul,
    two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using Prf.andI canon result

theorem compact_ordered_rate (X Y D sign K T U L : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hk : Γ ⊢[PRAAx] le D (K*X)) (ht : Γ ⊢[PRAAx] le one T) (hu : Γ ⊢[PRAAx] le T U) :
    Γ ⊢[PRAAx] independentRate F F (cutData X Y D sign T L) (cutData X Y D sign U L) (two*K) T := by
  let e := cutoff L
  let a := width T L
  let b := width U L
  let d := monus U T
  let c := e*d
  let x := cutData X Y D sign T L
  let y := cutData X Y D sign U L
  have he := cutoff_positive (Γ := Γ) L
  have hU : Γ ⊢[PRAAx] le one U := le_trans ht hu
  have hx := cut_regular X Y D sign T L hz ht
  have hy := cut_regular X Y D sign U L hz hU
  have sourceT := panel_source X D sign T L hz ht
  have equation := eq_add_of_le hu
  refine .orE (zero_or_succ d) ?_ ?_
  · let Δ := (d ≐ zero)::Γ
    have ut : Δ ⊢[PRAAx] U ≐ T :=
      equation.wk.eqTrans ((congrAdd (.eqRefl T) Prf.hyp0).eqTrans (add_zero T))
    have widths : Δ ⊢[PRAAx] b ≐ a := congrMonus (congrMul (.eqRefl e) ut) (.eqRefl one)
    have eq : Δ ⊢[PRAAx] x ≐ y :=
      data_congr X Y D sign ut.eqSymm (.eqRefl one) widths.eqSymm (.eqRefl e)
    have self := GaussianNamedDifferenceRate.self_rate (Γ := Δ) F x hx.wk
    have nonnegative : Δ ⊢[PRAAx] le (zero*T) ((two*K)*one) := by ipra_le 2*𝔞(K)
    have r := GaussianNamedRateRadius.weaken F F x x zero one (two*K) T (le_refl one) ht.wk nonnegative self
    exact GaussianNamedRateTransport.transport F F F F x x x y _ _ ht.wk r
      (cross_refl _ _ hx.wk) (cross_data_congr _ _ x y x x eq (.eqRefl _) (cross_refl _ _ hx.wk))
  · let Δ := (d ≐ succ (pred d))::Γ
    let left := panel X Y D sign U one a e
    let full := panel X Y D sign U one (a+c) e
    let right := panel X Y D sign U (one+a) c e
    have dz : Δ ⊢[PRAAx] le one d :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred d))
    have hc : Δ ⊢[PRAAx] le one c := positive_product _ _ he.wk dz
    have ha : Δ ⊢[PRAAx] le one a := (GaussianBinetBoseOriginExhaustion.width_positive T L ht).wk
    have et : Δ ⊢[PRAAx] e*T ≐ one+a := (endpoint T L ht).wk
    have eu : Δ ⊢[PRAAx] e*U ≐ one+(a+c) :=
      (congrMul (.eqRefl e) equation.wk).eqTrans
        ((by dsimp only [c]; ipra_ring : Δ ⊢[PRAAx] e*(T+d) ≐ e*T+c).eqTrans
          ((congrAdd et (.eqRefl c)).eqTrans (by ipra_ring)))
    have ew : Δ ⊢[PRAAx] b ≐ a+c :=
      (congrMonus (eu.eqTrans (by ipra_ring)) (.eqRefl one)).eqTrans (add_monus _ _)
    have leftSource : Δ ⊢[PRAAx] GaussianBinetBoseCompact.source X D sign U one a e :=
      .andI hz.wk (.andI (le_refl one) (.andI he.wk
        (le_congr et (.eqRefl _) (le_mul_mono (le_refl e) hu.wk))))
    have fullSource : Δ ⊢[PRAAx] GaussianBinetBoseCompact.source X D sign U one (a+c) e :=
      .andI hz.wk (.andI (le_refl one) (.andI he.wk (le_congr eu (.eqRefl _) (le_refl _))))
    have rightSource : Δ ⊢[PRAAx] GaussianBinetBoseCompact.source X D sign U (one+a) c e :=
      .andI hz.wk (.andI (le_add_right one a) (.andI he.wk
        (le_congr (eu.eqTrans (by ipra_ring)) (.eqRefl _) (le_refl _))))
    have fold := additivity X Y D sign U one a c e fullSource ha hc
    have r := GaussianNamedSmallAddendRate.independent_rate F F F left full right (two*K*e) (one+a)
      (le_add_right one a)
      (GaussianBinetBoseCompact.regular X Y D sign U one a e leftSource)
      (GaussianBinetBoseCompact.regular X Y D sign U one (a+c) e fullSource)
      (GaussianBinetBoseCompact.regular X Y D sign U (one+a) c e rightSource) fold
      (tail_samples X Y D sign U (one+a) c e K rightSource hc hk.wk)
    have budget : Δ ⊢[PRAAx] le ((two*K*e)*T) ((two*K)*(one+a)) :=
      le_of_eq_add (d := zero)
        ((by ipra_ring : Δ ⊢[PRAAx] (two*K)*(one+a) ≐ (two*K)*(one+a)+zero).eqTrans
          ((congrAdd (congrMul (.eqRefl (two*K)) et.eqSymm) (.eqRefl zero)).eqTrans (by ipra_ring)))
    have ru := GaussianNamedRateRadius.weaken F F left full _ _ _ _ (le_add_right one a) ht.wk budget r
    have eqLeft : Δ ⊢[PRAAx] crossEquivalent F F x left :=
      GaussianCompactMeshIndependence.name_independence evaluatorF (e+one) a e (gain D e T) T (gain D e U) U
        (fixedData X Y D sign)
        (.andI (GaussianBinetBoseCompact.compact_input X Y D sign T one a e sourceT.wk)
          (GaussianBinetBoseCompact.compact_input X Y D sign U one a e leftSource))
    have eqFull : Δ ⊢[PRAAx] crossEquivalent F F y full :=
      cross_data_congr F F y y y full (.eqRefl _) (data_congr X Y D sign (.eqRefl U) (.eqRefl one) ew (.eqRefl e))
        (cross_refl F y hy.wk)
    exact GaussianNamedRateTransport.transport F F F F left full x y _ _ ht.wk ru eqLeft eqFull

private theorem observation_slack (p q t X Y D sign K T U : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hk : Γ ⊢[PRAAx] le D (K*X)) (ht : Γ ⊢[PRAAx] le one T) (hu : Γ ⊢[PRAAx] le T U) :
    Γ ⊢[PRAAx] GaussianRationalSlackRemoval.slack
      (GaussianRationalMetric.qsub (ap2 P p (origin X Y D sign T)) (ap2 P q (origin X Y D sign U)))
      (rateNumerator (two*K) T p q) (rateDenominator T p q) (two*two) t := by
  let L := schedule p D+schedule q D
  let Z := rateDenominator T p q*unit t
  have z : Γ ⊢[PRAAx] le one Z := positive_product _ _ (denominator_positive T p q ht) (unit_positive t)
  have leftRaw := late_observations p t X Y D sign T L (.andI hz ht) (le_add_right _ _)
  have rightRaw := late_observations q t X Y D sign U L (.andI hz (le_trans ht hu)) (le_add_left _ _)
  have left := distance_radius_mono _ _ _ _ ((unit p+unit t)*(T*unit q)) Z
    (positive_product _ _ (unit_positive p) (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring)) leftRaw
  have middle := distance_radius_mono _ _ _ _ ((two*K*unit t+two*T)*(unit p*unit q)) Z
    (positive_product _ _ ht (unit_positive t)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    (GaussianNamedInverseRate.diagonal_rate F F (cutData X Y D sign T L) (cutData X Y D sign U L)
      (two*K) T t ht (compact_ordered_rate X Y D sign K T U L hz hk ht hu))
  have rightReversed : Γ ⊢[PRAAx] distanceBounded (ap2 F t (cutData X Y D sign U L))
      (ap2 P q (origin X Y D sign U)) (unit t+unit q) (unit t*unit q) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive t)) rightRaw)
  have right := distance_radius_mono _ _ _ _ ((unit t+unit q)*(T*unit p)) Z
    (positive_product _ _ (unit_positive t) (unit_positive q)) z
    (le_of_eq_add (d := zero) (by dsimp only [Z,rateDenominator]; ipra_ring))
    rightReversed
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [rateNumerator,rateDenominator,unit]; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ z (distance_triangle_same _ _ _ _ _ _ z left middle) right)

theorem observations (p q X Y D sign K T U : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hk : Γ ⊢[PRAAx] le D (K*X)) (ht : Γ ⊢[PRAAx] le one T) (hu : Γ ⊢[PRAAx] le T U) :
    Γ ⊢[PRAAx] distanceBounded (ap2 P p (origin X Y D sign T)) (ap2 P q (origin X Y D sign U))
      (rateNumerator (two*K) T p q) (rateDenominator T p q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (two*two) (denominator_positive T p q ht)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have zs : Δ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (s X) (s D) (s sign) := by
    simpa [Δ,s,Fm.shift,Syn.shift,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source] using hz.shift
  have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hk.shift
  have ts : Δ ⊢[PRAAx] le one (s T) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using ht.shift
  have us : Δ ⊢[PRAAx] le (s T) (s U) := by simpa [Δ,s,Fm.shift,Syn.shift] using hu.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,
    GaussianNamedInverseRate.subst_rateNumerator,GaussianNamedInverseRate.subst_rateDenominator,
    GaussianBinetBoseOriginName.subst_data,PTm.subst_mul,Δ,s,Syn.shift,ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] using
    observation_slack (s p) (s q) (var 0) (s X) (s Y) (s D) (s sign) (s K) (s T) (s U) zs ks ts us

theorem ordered_rate (X Y D sign K T U : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hk : Γ ⊢[PRAAx] le D (K*X)) (ht : Γ ⊢[PRAAx] le one T) (hu : Γ ⊢[PRAAx] le T U) :
    Γ ⊢[PRAAx] independentRate P P (origin X Y D sign T) (origin X Y D sign U) (two*K) T := by
  refine .allI (.allI ?_)
  let s (v : PTm n) := Syn.shift (Syn.shift v)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have zs : Δ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source (s X) (s D) (s sign) := by
    simpa [Δ,s,Fm.shift,Syn.shift,GaussianRightHalfPlaneLogarithm.source,GaussianRightHalfPlaneArgument.source] using hz.shift.shift
  have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hk.shift.shift
  have ts : Δ ⊢[PRAAx] le one (s T) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using ht.shift.shift
  have us : Δ ⊢[PRAAx] le (s T) (s U) := by simpa [Δ,s,Fm.shift,Syn.shift] using hu.shift.shift
  simpa only [independentRate,Δ,s,Syn.shift,GaussianBinetBoseOriginName.subst_data,PTm.subst_mul,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    observations (var 1) (var 0) (s X) (s Y) (s D) (s sign) (s K) (s T) (s U) zs ks ts us

theorem actual_second_Binet_ordered_horizon_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶ le (var 2) (var 4*var 0) ⟶
      le one (var 5) ⟶ le (var 5) (var 6) ⟶ independentRate P P
        (origin (var 0) (var 1) (var 2) (var 3) (var 5)) (origin (var 0) (var 1) (var 2) (var 3) (var 6))
        (two*var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (ordered_rate _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk hyp2 Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseHorizonRate
