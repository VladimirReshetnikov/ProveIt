import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceExhaustion
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius

/-!
# The actual Binet prefix rate at two ordered exhaustion cutoffs

Each panel starts at zero, with its own physical upper endpoint as
the time horizon. Move the smaller panel to the common larger
horizon before applying the compact prefix theorem. Equal encoded
widths follow from regularity of the same original name.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceOrderedPrefixes

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetLaplaceStrip (nameF data)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianNameEquivalence (crossEquivalent cross_refl)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (positive_product)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num pred)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => nameF GaussianBinetLaplaceStrip.Kernel.cofinal

abbrev width (D L : PTm n) : PTm n := D*L*one
def prefixData (X Y D sign R L : PTm n) : PTm n :=
  data X Y D sign R (width D L) zero zero (width D L) one

@[simp] theorem subst_prefixData {m : ℕ} (σ : Fin n → PTm m) (X Y D sign R L : PTm n) :
    Syn.subst σ (prefixData X Y D sign R L) =
      prefixData (Syn.subst σ X) (Syn.subst σ Y) (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ R) (Syn.subst σ L) := by
  simp [prefixData,width,one,ConciseIPRA.PTm.subst_zero]

private theorem panel_source (X Y D sign R T W : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R)
    (hw : Γ ⊢[PRAAx] le W T) : Γ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R T zero W one :=
  .andI h (.andI (le_refl one) (le_congr (zero_add W).eqSymm (one_mul T).eqSymm hw))

theorem prefix_regular (X Y D sign R L : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R) :
    Γ ⊢[PRAAx] pointCN F (prefixData X Y D sign R L) :=
  GaussianBinetLaplaceStrip.regular .cofinal X Y D sign R (width D L) zero zero (width D L) one
    (panel_source X Y D sign R _ _ h (le_refl _))

private theorem data_congr (X Y D sign R T T' W W' : PTm n)
    (ht : Γ ⊢[PRAAx] T ≐ T') (hw : Γ ⊢[PRAAx] W ≐ W') : Γ ⊢[PRAAx]
    data X Y D sign R T zero zero W one ≐ data X Y D sign R T' zero zero W' one := by
  have first : Γ ⊢[PRAAx] data X Y D sign R T zero zero W one ≐ data X Y D sign R T' zero zero W one := by
    simpa only [GaussianBinetLaplaceStrip.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      Prf.eqCongr1 (data (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift R)
        (var 0) zero zero (Syn.shift W) one) ht
  have second : Γ ⊢[PRAAx] data X Y D sign R T' zero zero W one ≐ data X Y D sign R T' zero zero W' one := by
    simpa only [GaussianBinetLaplaceStrip.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
      Prf.eqCongr1 (data (Syn.shift X) (Syn.shift Y) (Syn.shift D) (Syn.shift sign) (Syn.shift R)
        (Syn.shift T') zero zero (var 0) one) hw
  exact first.eqTrans second

theorem ordered_rate (X Y D sign R L K : PTm n) (h : Γ ⊢[PRAAx] source X Y D sign R)
    (hL : Γ ⊢[PRAAx] le one L) (hLK : Γ ⊢[PRAAx] le L K) : Γ ⊢[PRAAx]
    independentRate F F (prefixData X Y D sign R L) (prefixData X Y D sign R K)
      D (num 12*X*unit L) := by
  let a := width D L
  let b := width D K
  let c := monus b a
  let x := prefixData X Y D sign R L
  let y := prefixData X Y D sign R K
  let P := num 12*X*unit L
  have hX := h.andE₁.andE₁.andE₁
  have hP : Γ ⊢[PRAAx] le one P :=
    positive_product _ _ (positive_product _ _ (by ipra_le 11) hX) (unit_positive L)
  have hab : Γ ⊢[PRAAx] le a b := le_mul_mono (le_mul_mono (le_refl D) hLK) (le_refl one)
  have ec : Γ ⊢[PRAAx] b ≐ a+c := eq_add_of_le hab
  have hx := prefix_regular X Y D sign R L h
  have hy := prefix_regular X Y D sign R K h
  refine .orE (zero_or_succ c) ?_ ?_
  · have same : (c ≐ zero)::Γ ⊢[PRAAx] b ≐ a :=
      ec.wk.eqTrans ((congrAdd (.eqRefl a) Prf.hyp0).eqTrans (add_zero a))
    have ep : (c ≐ zero)::Γ ⊢[PRAAx] x ≐ y :=
      data_congr X Y D sign R _ _ _ _ same.eqSymm same.eqSymm
    have r := GaussianNamedDifferenceRate.self_rate (Γ := (c ≐ zero)::Γ) F x hx.wk
    have rel := GaussianNamedRateRadius.weaken F F x x zero one D P (le_refl one) hP.wk
      (by ipra_le Groth.ι (IPRA.Q.mk ((c ≐ zero)::Γ) D)) r
    exact GaussianNamedRateTransport.transport F F F F x x x y _ _ hP.wk rel
      (cross_refl _ _ hx.wk) (cross_data_congr _ _ x y x x ep (.eqRefl _) (cross_refl _ _ hx.wk))
  · let Δ := (c ≐ succ (pred c))::Γ
    let s := data X Y D sign R b zero zero a one
    let t := data X Y D sign R b zero zero (a+c) one
    have hc : Δ ⊢[PRAAx] le one c := le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ (pred c))
    have hwide : Δ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R b zero (a+c) one :=
      panel_source X Y D sign R _ _ h.wk (le_congr ec.wk (.eqRefl _) (le_refl b))
    have hsmall : Δ ⊢[PRAAx] GaussianBinetLaplaceStrip.source X Y D sign R b zero a one :=
      panel_source X Y D sign R _ _ h.wk hab.wk
    have eq1 : Δ ⊢[PRAAx] crossEquivalent F F x s :=
      GaussianBinetLaplaceStripHorizon.coherence .cofinal X Y D sign R a R b zero zero a one
        (panel_source X Y D sign R _ _ h.wk (le_refl a)) hsmall
    have e : Δ ⊢[PRAAx] y ≐ t := data_congr X Y D sign R _ _ _ _ (.eqRefl _) ec.wk
    have eq2 : Δ ⊢[PRAAx] crossEquivalent F F y t :=
      cross_data_congr F F y y y t (.eqRefl _) e (cross_refl F y hy.wk)
    exact GaussianNamedRateTransport.transport F F F F s t x y D P hP.wk
      (GaussianBinetLaplaceExhaustion.prefix_rate X Y D sign R b zero L c one hwide hL.wk hc) eq1 eq2

theorem actual_Binet_ordered_prefix_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let X := var 0
     let Y := var 1
     let D := var 2
     let sign := var 3
     let R := var 4
     let L := var 5
     let K := var 6
     source X Y D sign R ⟶ le one L ⟶ le L K ⟶
       independentRate F F (prefixData X Y D sign R L) (prefixData X Y D sign R K) D (num 12*X*unit L)) :=
  closeUniv 7 (.impI (.impI (.impI (ordered_rate _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceOrderedPrefixes
