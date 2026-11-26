import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Improper.GaussianBinetLaplaceMomentHorizon
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.GaussianBinetLaplaceMomentAdditivity
import IPRADerivations.Analysis.Stirling.Binet.Laplace.Moments.Improper.GaussianBinetLaplaceMomentTail
import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallAddendRate
import IPRADerivations.Analysis.Names.Rates.Transport.GaussianNamedRateTransport

/-!
# Ordered compact prefixes of the actual weighted Binet moments

Two ordered horizons give the independent prefix rate by exact strip
additivity, the far-tail bound, and horizon coherence of the unchanged
left interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentPrefixes

open_ipra
open GaussianBinetLaplaceMomentCompact (data regular)
open GaussianBinetLaplaceMomentFloor (nameF evaluatorF fixedData gain)
open GaussianBinetLaplaceMomentTail (coefficient)
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedSmallAddendRate (tailSamples)
open GaussianRationalHorner (canonical)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "stripSource" => GaussianBinetLaplaceStrip.source
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def prefixData (j X D R L : PTm n) : PTm n := data j X D R L zero L one
def tailNumerator (j D : PTm n) : PTm n := two*coefficient j D

ipra_subst prefixData [one]

ipra_subst tailNumerator [two, one]

private theorem panel_source (X D R K A C : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hc : Γ ⊢[PRAAx] le (A+C) K) :
    Γ ⊢[PRAAx] stripSource X zero D zero R K A C one :=
  .andI h (.andI (le_refl one) (le_congr (.eqRefl _) (one_mul _).eqSymm hc))

theorem prefix_regular (j X D R L : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] pointCN nameF (prefixData j X D R L) :=
  regular j X D R L zero L one (panel_source X D R L zero L h (le_congr (zero_add _).eqSymm (.eqRefl _) (le_refl _)))

private theorem tail_samples (j X D R K L C : PTm n)
    (h : Γ ⊢[PRAAx] stripSource X zero D zero R K L C one)
    (hL : Γ ⊢[PRAAx] le one L) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] tailSamples nameF (data j X D R K L C one) (tailNumerator j D) L := by
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hs : Δ ⊢[PRAAx] stripSource (s X) zero (s D) zero (s R) (s K) (s L) (s C) one := by
    simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,one,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using h.shift
  have l : Δ ⊢[PRAAx] le one (s L) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hL.shift
  have c : Δ ⊢[PRAAx] le one (s C) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hC.shift
  have hc : Δ ⊢[PRAAx] canonical (ap2 nameF p (data (s j) (s X) (s D) (s R) (s K) (s L) (s C) one)) :=
    GaussianCompactRiemannName.name_canonical evaluatorF p (one+s L) (s C) one
      (gain (s j) (s R) (s K)) (s K) (fixedData (s j) (s X) (s D) (s R) (s K))
  have hb : Δ ⊢[PRAAx] bounded (ap2 nameF p (data (s j) (s X) (s D) (s R) (s K) (s L) (s C) one))
      (tailNumerator (s j) (s D)*unit p+s L) (s L*unit p) :=
    bound_congr (.eqRefl _) (by unfold tailNumerator; ipra_ring) (by ipra_ring)
      (GaussianBinetLaplaceMomentTail.name_bound p (s j) (s X) (s D) (s R) (s K) (s L) (s C) one hs l c)
  simpa only [tailSamples,Δ,s,p,Syn.shift,subst_tailNumerator,GaussianBinetLaplaceMomentCompact.subst_data,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using Prf.andI hc hb

private theorem panel_width_congr (j X D R T A C C' : PTm n) (e : Γ ⊢[PRAAx] C ≐ C') :
    Γ ⊢[PRAAx] data j X D R T A C one ≐ data j X D R T A C' one := by
  simpa only [GaussianBinetLaplaceMomentCompact.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    Prf.eqCongr1 (data (Syn.shift j) (Syn.shift X) (Syn.shift D) (Syn.shift R) (Syn.shift T)
      (Syn.shift A) (var 0) one) e

private theorem same_horizon_rate (j X D R K L C : PTm n)
    (h : Γ ⊢[PRAAx] realSource X zero D zero R) (hw : Γ ⊢[PRAAx] le (L+C) K)
    (hL : Γ ⊢[PRAAx] le one L) (hC : Γ ⊢[PRAAx] le one C) :
    Γ ⊢[PRAAx] independentRate nameF nameF (data j X D R K zero L one)
      (data j X D R K zero (L+C) one) (tailNumerator j D) L := by
  have left := panel_source X D R K zero L h
    (le_congr (zero_add _).eqSymm (.eqRefl _) (le_trans (le_add_right _ _) hw))
  have right := panel_source X D R K L C h hw
  have full := panel_source X D R K zero (L+C) h (le_congr (zero_add _).eqSymm (.eqRefl _) hw)
  let x := data j X D R K zero L one
  let y := data j X D R K zero (L+C) one
  let z := data j X D R K L C one
  let z' := data j X D R K (zero+L) C one
  have eq : Γ ⊢[PRAAx] z' ≐ z := by
    simpa only [z,z',GaussianBinetLaplaceMomentCompact.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      Prf.eqCongr1 (data (Syn.shift j) (Syn.shift X) (Syn.shift D) (Syn.shift R) (Syn.shift K)
        (var 0) (Syn.shift C) one) (zero_add L)
  have e : Γ ⊢[PRAAx] addData x z' ≐ addData x z := by
    simpa only [GaussianNameArithmetic.subst_addData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
      Prf.eqCongr1 (addData (Syn.shift x) (var 0)) eq
  have split : Γ ⊢[PRAAx] crossEquivalent nameF (addF nameF nameF) y (addData x z) :=
    cross_data_congr nameF (addF nameF nameF) _ _ _ _ (.eqRefl _) e
      (GaussianBinetLaplaceMomentAdditivity.additivity j X D R K zero L C one full hL hC)
  exact GaussianNamedSmallAddendRate.independent_rate nameF nameF nameF x y z _ _ hL
    (regular j X D R K zero L one left) (regular j X D R K zero (L+C) one full)
    (regular j X D R K L C one right) split (tail_samples j X D R K L C right hL hC)

theorem ordered_rate (j X D R L K : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hL : Γ ⊢[PRAAx] le one L) (hle : Γ ⊢[PRAAx] le L K) :
    Γ ⊢[PRAAx] independentRate nameF nameF (prefixData j X D R L) (prefixData j X D R K) (tailNumerator j D) L := by
  let C := monus K L
  let x := prefixData j X D R L
  let y := prefixData j X D R K
  have ec : Γ ⊢[PRAAx] K ≐ L+C := eq_add_of_le hle
  have hx := prefix_regular j X D R L h
  have hy := prefix_regular j X D R K h
  refine .orE (zero_or_succ C) ?_ ?_
  · have same : (C ≐ zero)::Γ ⊢[PRAAx] K ≐ L :=
      ec.wk.eqTrans ((congrAdd (.eqRefl L) Prf.hyp0).eqTrans (add_zero L))
    have ex : (C ≐ zero)::Γ ⊢[PRAAx] x ≐ y := by
      simpa only [x,y,subst_prefixData,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var] using
        Prf.eqCongr1 (prefixData (Syn.shift j) (Syn.shift X) (Syn.shift D) (Syn.shift R) (var 0)) same.eqSymm
    have step := GaussianNamedDifferenceRate.self_rate (Γ := (C ≐ zero)::Γ) nameF x hx.wk
    have widened := GaussianNamedRateRadius.weaken nameF nameF x x zero one (tailNumerator j D) L
      (le_refl one) hL.wk (by ipra_le Groth.ι (Q.mk ((C ≐ zero)::Γ) (tailNumerator j D))) step
    exact GaussianNamedRateTransport.transport nameF nameF nameF nameF x x x y _ _ hL.wk widened
      (cross_refl _ _ hx.wk) (cross_data_congr _ _ x y x x ex (.eqRefl _) (cross_refl _ _ hx.wk))
  · let Δ := (C ≐ succ (pred C))::Γ
    let u := data j X D R K zero L one
    let v := data j X D R K zero (L+C) one
    have hc : Δ ⊢[PRAAx] le one C := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred C))
    have hw : Δ ⊢[PRAAx] le (L+C) K := le_congr ec.wk (.eqRefl _) (le_refl K)
    have first : Δ ⊢[PRAAx] crossEquivalent nameF nameF x u :=
      GaussianBinetLaplaceMomentHorizon.coherence j X D R L R K zero L one
        (panel_source X D R L zero L h.wk (le_congr (zero_add _).eqSymm (.eqRefl _) (le_refl L)))
        (panel_source X D R K zero L h.wk (le_congr (zero_add _).eqSymm (.eqRefl _) hle.wk))
    have e : Δ ⊢[PRAAx] y ≐ v := panel_width_congr j X D R K zero K (L+C) ec.wk
    have second : Δ ⊢[PRAAx] crossEquivalent nameF nameF y v :=
      cross_data_congr nameF nameF y y y v (.eqRefl _) e (cross_refl nameF y hy.wk)
    exact GaussianNamedRateTransport.transport nameF nameF nameF nameF u v x y _ _ hL.wk
      (same_horizon_rate j X D R K L C h.wk hw hL.wk hc) first second

theorem actual_weighted_Binet_ordered_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (realSource (var 1) zero (var 2) zero (var 3) ⟶ le one (var 4) ⟶ le (var 4) (var 5) ⟶
      independentRate nameF nameF (prefixData (var 0) (var 1) (var 2) (var 3) (var 4))
        (prefixData (var 0) (var 1) (var 2) (var 3) (var 5)) (tailNumerator (var 0) (var 2)) (var 4)) :=
  closeUniv 6 (.impI (.impI (.impI (ordered_rate _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentPrefixes
