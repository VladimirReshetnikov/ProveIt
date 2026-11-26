import IPRADerivations.Analysis.Stirling.Binet.Bose.CompactIntegrand.GaussianBinetBoseCompactAlignment
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# Dyadic exhaustion of the original Bose integral at the origin

At a fixed positive integer horizon, put two starting times over the
later dyadic denominator. The only added interval has width at most
the former starting time. Its actual compact sample bound therefore
gives a cutoff rate independent of the horizon.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseOriginExhaustion

open_ipra
open GaussianBinetBoseCompact (nameF data source)
open GaussianBinetBoseCompactAlignment (data_congr rescale left_gap_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def cutoff (L : PTm n) : PTm n := unit (succ L)
def width (T L : PTm n) : PTm n := monus (cutoff L*T) one
def cutData (X Y D sign T L : PTm n) : PTm n :=
  data X Y D sign T one (width T L) (cutoff L)

ipra_subst cutoff
ipra_subst width [one]
ipra_subst cutData [one]

theorem cutoff_twice (L : PTm n) : Γ ⊢[PRAAx] cutoff L ≐ two*unit L :=
  (pw_succ two L).eqTrans (mul_comm _ _)

theorem cutoff_positive (L : PTm n) : Γ ⊢[PRAAx] le one (cutoff L) := unit_positive (succ L)

theorem endpoint (T L : PTm n) (hT : Γ ⊢[PRAAx] le one T) :
    Γ ⊢[PRAAx] cutoff L*T ≐ one+width T L :=
  eq_add_of_le (positive_product _ _ (cutoff_positive L) hT)

theorem width_positive (T L : PTm n) (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx] le one (width T L) := by
  have initial : Γ ⊢[PRAAx] le two (cutoff L) :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] two*one ≐ two) (cutoff_twice L).eqSymm (le_mul_mono (le_refl two) (unit_positive L))
  have order : Γ ⊢[PRAAx] le two (one+width T L) := le_congr (.eqRefl _) (endpoint T L hT)
    (le_trans initial (le_congr (by ipra_ring : Γ ⊢[PRAAx] cutoff L*one ≐ cutoff L) (.eqRefl _) (le_mul_mono (le_refl (cutoff L)) hT)))
  ipra_le sl order

theorem panel_source (X D sign T L : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx] source X D sign T one (width T L) (cutoff L) :=
  .andI hz (.andI (le_refl one) (.andI (cutoff_positive L) (le_congr (endpoint T L hT) (.eqRefl _) (le_refl _))))

theorem cut_regular (X Y D sign T L : PTm n) (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hT : Γ ⊢[PRAAx] le one T) : Γ ⊢[PRAAx] pointCN nameF (cutData X Y D sign T L) :=
  GaussianBinetBoseCompact.regular X Y D sign T one (width T L) (cutoff L) (panel_source X D sign T L hz hT)

theorem cutoff_multiple (L K : PTm n) (h : Γ ⊢[PRAAx] le L K) :
    Γ ⊢[PRAAx] cutoff K ≐ unit (monus K L)*cutoff L := by
  have el : Γ ⊢[PRAAx] succ K ≐ succ L+monus K L :=
    (congrSucc (eq_add_of_le h)).eqTrans (by ipra_ring)
  have power : Γ ⊢[PRAAx] unit (succ K) ≐ unit (succ L+monus K L) := by
    simpa only [GaussianCoefficientNameBounds.subst_unit,Syn.inst_zero,Syn.subst_var] using
      Prf.eqCongr1 (unit (var 0)) el
  exact power.eqTrans ((pw_add two (succ L) (monus K L)).eqTrans (mul_comm _ _))

theorem ordered_rate (X Y D sign T L K : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hT : Γ ⊢[PRAAx] le one T) (hLK : Γ ⊢[PRAAx] le L K) : Γ ⊢[PRAAx]
    independentRate nameF nameF (cutData X Y D sign T L) (cutData X Y D sign T K)
      D (cutoff L*(num 4*X)) := by
  let e := cutoff L
  let f := cutoff K
  let k := unit (monus K L)
  let c := monus k one
  let w := width T L
  let v := width T K
  let x := cutData X Y D sign T L
  let y := cutData X Y D sign T K
  let P := e*(num 4*X)
  let Q := f*(num 4*X)
  have hX4 : Γ ⊢[PRAAx] le one (num 4*X) := positive_product _ _ (by ipra_le 3) hz.andE₁.andE₁
  have hp : Γ ⊢[PRAAx] le one P := positive_product _ _ (cutoff_positive L) hX4
  have hq : Γ ⊢[PRAAx] le one Q := positive_product _ _ (cutoff_positive K) hX4
  have hx := cut_regular X Y D sign T L hz hT
  have hy := cut_regular X Y D sign T K hz hT
  have hk : Γ ⊢[PRAAx] le one k := unit_positive _
  have fEq : Γ ⊢[PRAAx] f ≐ k*e := cutoff_multiple L K hLK
  have kEq : Γ ⊢[PRAAx] k ≐ one+c := eq_add_of_le hk
  have cut := panel_source X D sign T L hz hT
  refine .orE (zero_or_succ c) ?_ ?_
  · let Δ := (c ≐ zero)::Γ
    have eqOne : Δ ⊢[PRAAx] k ≐ one :=
      kEq.wk.eqTrans ((congrAdd (.eqRefl one) Prf.hyp0).eqTrans (add_zero one))
    have ef : Δ ⊢[PRAAx] f ≐ e :=
      fEq.wk.eqTrans ((congrMul eqOne (.eqRefl e)).eqTrans (one_mul e))
    have ev : Δ ⊢[PRAAx] v ≐ w := congrMonus (congrMul ef (.eqRefl T)) (.eqRefl one)
    have same : Δ ⊢[PRAAx] x ≐ y :=
      data_congr X Y D sign (.eqRefl T) (.eqRefl one) ev.eqSymm ef.eqSymm
    have self := GaussianNamedDifferenceRate.self_rate (Γ := Δ) nameF x hx.wk
    have weakened := GaussianNamedRateRadius.weaken nameF nameF x x zero one D P (le_refl one) hp.wk
      (by ipra_le Groth.ι (IPRA.Q.mk Δ D)) self
    exact GaussianNamedRateTransport.transport nameF nameF nameF nameF x x x y D P hp.wk weakened
      (cross_refl _ _ hx.wk) (cross_data_congr _ _ x y x x same (.eqRefl _) (cross_refl _ _ hx.wk))
  · let Δ := (c ≐ succ (pred c))::Γ
    let short := data X Y D sign T (one+c) (k*w) f
    let full := data X Y D sign T one (c+k*w) f
    have hc : Δ ⊢[PRAAx] le one c := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred c))
    have hw : Δ ⊢[PRAAx] le one (k*w) := positive_product _ _ hk.wk (width_positive T L hT).wk
    have beginEq : Δ ⊢[PRAAx] one+c ≐ k*one := kEq.wk.eqSymm.eqTrans (by ipra_ring : Δ ⊢[PRAAx] k ≐ k*one)
    have fullEq : Δ ⊢[PRAAx] f*T ≐ one+(c+k*w) := by
      have first : Δ ⊢[PRAAx] f*T ≐ k*(one+w) :=
        (congrMul fEq.wk (.eqRefl T)).eqTrans
          ((by ipra_ring : Δ ⊢[PRAAx] k*e*T ≐ k*(e*T)).eqTrans (congrMul (.eqRefl k) (endpoint T L hT).wk))
      exact first.eqTrans ((by ipra_ring : Δ ⊢[PRAAx] k*(one+w) ≐ k+k*w).eqTrans
        ((congrAdd kEq.wk (.eqRefl _)).eqTrans (by ipra_ring)))
    have widthEq : Δ ⊢[PRAAx] v ≐ c+k*w :=
      (congrMonus (fullEq.eqTrans (by ipra_ring)) (.eqRefl one)).eqTrans (add_monus _ _)
    have hfull : Δ ⊢[PRAAx] source X D sign T one (c+k*w) f :=
      .andI hz.wk (.andI (le_refl one) (.andI (cutoff_positive K) (le_congr fullEq (.eqRefl _) (le_refl _))))
    have ea : Δ ⊢[PRAAx] crossEquivalent nameF nameF x short :=
      cross_data_congr _ _ _ _ _ _ (.eqRefl _)
        (data_congr X Y D sign (.eqRefl T) beginEq.eqSymm (.eqRefl _) fEq.wk.eqSymm)
        (rescale X Y D sign T T one w e k cut.wk hk.wk cut.andE₂.andE₂.andE₂.wk)
    have eb : Δ ⊢[PRAAx] crossEquivalent nameF nameF y full :=
      cross_data_congr _ _ y y y full (.eqRefl _) (data_congr X Y D sign (.eqRefl T) (.eqRefl one) widthEq (.eqRefl f))
        (cross_refl _ _ hy.wk)
    have raw := left_gap_rate X Y D sign T one c (k*w) f hfull hc hw
    have cc : Δ ⊢[PRAAx] le c k := le_congr (.eqRefl _) kEq.wk.eqSymm (le_add_left c one)
    have wide : Δ ⊢[PRAAx] le (c*D*P) (D*Q) := by
      have fe : Δ ⊢[PRAAx] D*Q ≐ D*(k*e*(num 4*X)) := congrMul (.eqRefl D) (congrMul fEq.wk (.eqRefl _))
      have mono : Δ ⊢[PRAAx] le (c*D*P) (D*(k*e*(num 4*X))) := by
        dsimp only [P]
        ipra_le 𝔞(D*e*(num 4*X))*sl cc
      exact le_congr (.eqRefl _) fe.eqSymm mono
    exact GaussianNamedRateTransport.transport nameF nameF nameF nameF short full x y D P hp.wk
      (GaussianNamedRateRadius.weaken nameF nameF short full (c*D) Q D P hq.wk hp.wk wide raw) ea eb

theorem actual_second_Binet_dyadic_origin_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (GaussianRightHalfPlaneLogarithm.source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶ le (var 5) (var 6) ⟶
      independentRate nameF nameF (cutData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))
        (cutData (var 0) (var 1) (var 2) (var 3) (var 4) (var 6)) (var 2) (cutoff (var 5)*(num 4*var 0))) :=
  closeUniv 7 (.impI (.impI (.impI (ordered_rate _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseOriginExhaustion
