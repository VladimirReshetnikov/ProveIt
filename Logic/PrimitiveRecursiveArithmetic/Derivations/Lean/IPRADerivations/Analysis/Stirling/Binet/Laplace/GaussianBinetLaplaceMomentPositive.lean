import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentImproper
import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceMomentNonnegative
import IPRADerivations.Analysis.Names.GaussianNamedRealOrderEnvelope
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianNamedGammaHalfShift
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerRationalLogOrder

/-!
# A strict positive lower margin for every actual improper Binet moment

The fixed interval [1,2] has a positive rational lower margin for
every internal time power. Compact additivity attaches both
nonnegative exterior panels. Every original improper observation
uses a prefix containing this interval.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentPositive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentCompact (data regular)
open GaussianBinetLaplaceMomentFloor (unitPanelData unit_panel_floor_with_cap)
open GaussianBinetLaplaceMomentHorizon (coherence)
open GaussianBinetLaplaceMomentPrefixes (prefixData)
open GaussianBinetLaplaceRealFloor (floor floorDenominator floor_denominator_positive numerator_cap)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaCompactCutoffAlignment (cross_data_congr)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNamedRealOrderTransport (transport)
open GaussianRationalHorner (qadd qzero canonical ofGaussian_canonical positive_product)
open GaussianRationalSyntheticDivision (qzero_add)
open RationalValueBounds (upper upper_congr upper_mono)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianBinetLaplaceMomentFloor.nameF
local notation "J" => GaussianBinetLaplaceMomentImproper.nameF
local notation "JData" => GaussianBinetLaplaceMomentImproper.data
local notation "stripSource" => GaussianBinetLaplaceStrip.source
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def marginPoint (X : PTm n) : PTm n := radiusPoint two (floorDenominator X two)

@[simp] theorem subst_marginPoint {m : ℕ} (σ : Fin n → PTm m) (X : PTm n) :
    Syn.subst σ (marginPoint X) = marginPoint (Syn.subst σ X) := by simp [marginPoint,two,one]

private theorem margin_canonical (X : PTm n) : Γ ⊢[PRAAx] canonical (marginPoint X) :=
  ofGaussian_canonical _ _ (floor_denominator_positive X two)

private theorem radius_scalar (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] fstT (radiusPoint A B) ≐ fraction A B := by
  apply RationalFiniteSum.canonical_equal _ _ (ZT.ofNat A) (ZT.ofNat A) B B
    (ofGaussian_canonical _ _ hB).andE₂.andE₁ (RationalNormalForm.normalize_well_formed _ _ hB)
    (GaussianPositiveExponentialOrder.radius_real_representation A B hB) (fraction_represents A B hB) hB hB
  exact ZT.derive rfl

theorem margin_scalar (X : PTm n) : Γ ⊢[PRAAx] fstT (marginPoint X) ≐ floor X two :=
  radius_scalar two _ (floor_denominator_positive X two)

theorem panel_order (j X D R T A C E : PTm n)
    (h : Γ ⊢[PRAAx] stripSource X zero D zero R T A C E) :
    Γ ⊢[PRAAx] realOrder constantF F qzero (data j X D R T A C E) := by
  apply order_from_envelope constantF F qzero (data j X D R T A C E) one
    (constant_regular qzero) (regular j X D R T A C E h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] stripSource (s X) zero (s D) zero (s R) (s T) (s A) (s C) (s E) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianBinetLaplaceStrip.subst_source,ConciseIPRA.PTm.subst_zero] using h.shift
  have h0 : Δ ⊢[PRAAx] fstT qzero ≐ fraction zero one := radius_scalar zero one (le_refl one)
  have eq := (congrFst (constant_at (Γ := Δ) (var 0) qzero)).eqTrans h0
  simpa only [envelope,Δ,s,Syn.shift,GaussianBinetLaplaceMomentCompact.subst_data,
    GaussianRationalHorner.subst_qzero,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    upper_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (GaussianBinetLaplaceMomentNonnegative.panel_nonnegative (var 0) (s j) (s X) (s D) (s R) (s T) (s A) (s C) (s E) hs)

theorem unit_panel_order_with_cap (j X D R S : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] realOrder constantF F (marginPoint S) (unitPanelData j X D R) := by
  apply order_from_envelope constantF F (marginPoint S) (unitPanelData j X D R) (num 8)
    (constant_regular _) (GaussianBinetLaplaceMomentCompact.unit_panel_regular j X D R h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift
  have cap : Δ ⊢[PRAAx] le (s X) (s S*s D) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul] using hCap.shift
  have eq := (congrFst (constant_at (Γ := Δ) (var 0) (marginPoint (s S)))).eqTrans (margin_scalar (s S))
  simpa only [envelope,Δ,s,Syn.shift,subst_marginPoint,GaussianBinetLaplaceMomentFloor.subst_unitPanelData,
    LeanProofs.IPRA.PTm.subst_num] using
    upper_congr eq.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (unit_panel_floor_with_cap (var 0) (s j) (s X) (s D) (s R) (s S) hs cap)

theorem unit_panel_order (j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] realOrder constantF F (marginPoint X) (unitPanelData j X D R) :=
  unit_panel_order_with_cap j X D R X h (numerator_cap X D h.andE₁.andE₂)

private theorem split_order (j X D R T A C₁ C₂ a b c : PTm n)
    (h : Γ ⊢[PRAAx] stripSource X zero D zero R T A (C₁+C₂) one)
    (h₁ : Γ ⊢[PRAAx] le one C₁) (h₂ : Γ ⊢[PRAAx] le one C₂)
    (o₁ : Γ ⊢[PRAAx] realOrder constantF F a (data j X D R T A C₁ one))
    (o₂ : Γ ⊢[PRAAx] realOrder constantF F b (data j X D R T (A+C₁) C₂ one))
    (e : Γ ⊢[PRAAx] qadd a b ≐ c) :
    Γ ⊢[PRAAx] realOrder constantF F c (data j X D R T A (C₁+C₂) one) := by
  have sum := GaussianGammaEulerRationalLogOrder.add_order constantF F constantF F _ _ _ _ o₁ o₂
  have csum := GaussianNamedGammaHalfShift.constant_sum a b c e
  have split := GaussianBinetLaplaceMomentAdditivity.additivity j X D R T A C₁ C₂ one h h₁ h₂
  exact transport constantF (addF constantF constantF) (addF F F) F _ _ _ _
    (cross_symm _ _ _ _ csum) (cross_symm _ _ _ _ split) sum

private theorem panel_source (X D R L A C : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hc : Γ ⊢[PRAAx] le (A+C) L) : Γ ⊢[PRAAx] stripSource X zero D zero R L A C one :=
  .andI h (.andI (le_refl one) (le_congr (.eqRefl _) (one_mul _).eqSymm hc))

theorem prefix_order_with_cap (j X D R L S : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hL : Γ ⊢[PRAAx] le (num 3) L) (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] realOrder constantF F (marginPoint S) (prefixData j X D R L) := by
  let P : PTm n := one+one
  let C := one+monus L (num 3)
  let c := marginPoint S
  have ez : Γ ⊢[PRAAx] L ≐ P+C :=
    (eq_add_of_le hL).eqTrans (by dsimp only [P,C]; ipra_ring)
  have hP : Γ ⊢[PRAAx] le (zero+P) L :=
    le_trans (by dsimp only [P]; ipra_le 1) hL
  have hC : Γ ⊢[PRAAx] le one C := le_add_right _ _
  have left := panel_order j X D R L zero one one
    (panel_source X D R L zero one h (le_trans (by ipra_le 2) hL))
  have unit := unit_panel_order_with_cap j X D R S h hCap
  have unitSrc := panel_source X D R two one one h (le_of_eq_add (d := zero) (by ipra_ring))
  have rect := panel_source X D R L one one h (le_congr (zero_add P) (.eqRefl _) hP)
  have toL := coherence j X D R two R L one one one unitSrc rect
  let y := data j X D R L one one one
  let y' := data j X D R L (zero+one) one one
  have yEq : Γ ⊢[PRAAx] y ≐ y' := by
    simpa only [y,y',GaussianBinetLaplaceMomentCompact.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
        Prf.eqCongr1 (data (Syn.shift j) (Syn.shift X) (Syn.shift D) (Syn.shift R) (Syn.shift L) (var 0) one one)
          (zero_add one).eqSymm
  have mid := transport constantF constantF F F c c (unitPanelData j X D R) y'
    (cross_refl _ _ (constant_regular c))
    (cross_data_congr _ _ _ _ y y' (.eqRefl _) yEq toL) unit
  have zc : Γ ⊢[PRAAx] qadd qzero c ≐ c := qzero_add c (margin_canonical S)
  have first := split_order j X D R L zero one one qzero c c
    (panel_source X D R L zero P h hP) (le_refl one) (le_refl one) left mid zc
  have extWidth : Γ ⊢[PRAAx] le ((zero+P)+C) L :=
    le_congr ((add_assoc _ _ _).eqTrans (zero_add _)).eqSymm (.eqRefl _)
      (le_congr ez (.eqRefl _) (le_refl L))
  have ext := panel_order j X D R L (zero+P) C one
    (panel_source X D R L (zero+P) C h extWidth)
  have full := split_order j X D R L zero P C c qzero c
    (panel_source X D R L zero (P+C) h (le_congr (add_assoc _ _ _) (.eqRefl _) extWidth))
    (le_add_right one one) hC first ext
    ((GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans zc)
  have eq : Γ ⊢[PRAAx] data j X D R L zero (P+C) one ≐ prefixData j X D R L := by
    simpa only [prefixData,GaussianBinetLaplaceMomentCompact.subst_data,Syn.inst_zero,Syn.subst_inst_shift,Syn.subst_var,
      one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
        Prf.eqCongr1 (data (Syn.shift j) (Syn.shift X) (Syn.shift D) (Syn.shift R) (Syn.shift L) zero (var 0) one) ez.eqSymm
  exact transport constantF constantF F F c c _ _ (cross_refl _ _ (constant_regular c))
    (cross_data_congr _ _ _ _ _ _ (.eqRefl _) eq
      (cross_refl _ _ (regular j X D R L zero (P+C) one
        (panel_source X D R L zero (P+C) h (le_congr (add_assoc _ _ _) (.eqRefl _) extWidth))))) full

theorem prefix_order (j X D R L : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hL : Γ ⊢[PRAAx] le (num 3) L) :
    Γ ⊢[PRAAx] realOrder constantF F (marginPoint X) (prefixData j X D R L) :=
  prefix_order_with_cap j X D R L X h hL (numerator_cap X D h.andE₁.andE₂)

private theorem cutoff_contains_panel (p j D : PTm n) :
    Γ ⊢[PRAAx] le (num 3) (GaussianBinetLaplaceMomentImproper.cutoff p j D) := by
  let C := GaussianBinetLaplaceMomentPrefixes.tailNumerator j D
  have c : Γ ⊢[PRAAx] le (num 3) C := by
    dsimp [C,GaussianBinetLaplaceMomentPrefixes.tailNumerator,GaussianBinetLaplaceMomentTail.coefficient]
    ipra_le 2*𝔞(GaussianBinetLaplaceMomentDecay.tailScale j D)+5
  exact le_trans (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono c (unit_positive (succ p))))
    (GaussianBinetLaplaceMomentImproper.cutoff_budget p j D)

theorem improper_order_with_cap (j X D R S : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R)
    (hCap : Γ ⊢[PRAAx] le X (S*D)) :
    Γ ⊢[PRAAx] realOrder constantF J (marginPoint S) (JData j X D R) := by
  apply order_from_envelope constantF J (marginPoint S) (JData j X D R) two
    (constant_regular _) (GaussianBinetLaplaceMomentImproper.regular j X D R h)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let U := unit p
  let V := unit (succ p)
  let L := GaussianBinetLaplaceMomentImproper.cutoff p (s j) (s D)
  let m := marginPoint (s S)
  have hs : Δ ⊢[PRAAx] realSource (s X) zero (s D) zero (s R) :=
    by simpa only [Δ,s,Fm.shift,Syn.shift,GaussianLogGammaEulerResidualDomain.subst_source,
      ConciseIPRA.PTm.subst_zero] using h.shift
  have cap : Δ ⊢[PRAAx] le (s X) (s S*s D) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_le,PTm.subst_mul] using hCap.shift
  have positive := prefix_order_with_cap (s j) (s X) (s D) (s R) L (s S) hs (cutoff_contains_panel p (s j) (s D)) cap
  have raw := real_order_at constantF F m (prefixData (s j) (s X) (s D) (s R) L) (succ p) (succ p) positive
  have c := (constant_at (Γ := Δ) (succ p) m).eqTrans (constant_at p m).eqSymm
  have read := GaussianBinetLaplaceMomentImproper.sample_at (Γ := Δ) p (s j) (s X) (s D) (s R)
  have hv := unit_positive (Γ := Δ) (succ p)
  have retime := GaussianExponentialReference.unit_monotone (Γ := Δ) (le_succ_self p)
  have budget : Δ ⊢[PRAAx] le ((V+V)*U) (two*(V*V)) := by
    ipra_le 2*𝔞(V)*sl retime
  simpa only [envelope,Δ,s,p,m,U,Syn.shift,subst_marginPoint,GaussianBinetLaplaceMomentImproper.subst_data,
    two,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    upper_mono _ _ _ _ _ _ (positive_product _ _ hv hv)
      (upper_congr (congrFst c) (congrFst read).eqSymm (.eqRefl _) (.eqRefl _) raw) budget

theorem improper_order (j X D R : PTm n) (h : Γ ⊢[PRAAx] realSource X zero D zero R) :
    Γ ⊢[PRAAx] realOrder constantF J (marginPoint X) (JData j X D R) :=
  improper_order_with_cap j X D R X h (numerator_cap X D h.andE₁.andE₂)

theorem actual_improper_Binet_moments_uniform_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let j := var 0
     let X := var 1
     let D := var 2
     let R := var 3
     let S := var 4
     realSource X zero D zero R ⟶ le X (S*D) ⟶ realOrder constantF J (marginPoint S) (JData j X D R)) :=
  closeUniv 5 (.impI (.impI (improper_order_with_cap _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_improper_Binet_moments_positive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (realSource (var 1) zero (var 2) zero (var 3) ⟶ realOrder constantF J (marginPoint (var 1))
      (JData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (improper_order _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentPositive
