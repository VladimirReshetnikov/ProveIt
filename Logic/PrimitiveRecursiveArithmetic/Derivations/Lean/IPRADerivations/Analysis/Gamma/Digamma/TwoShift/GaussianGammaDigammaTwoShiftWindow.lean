import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftFiniteRate
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftTrapezoidGap

/-!
# Arithmetic of the two-shift window

The two shifted arguments have a common denominator b, with base a/b
and signed shifts of magnitude at most the positive integer A.
For a/b ≥ 2A+1 the finite estimate uses 4A(A+1)/(a/b).
-/

set_option autoImplicit false
set_option maxHeartbeats 3700000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftWindow

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaDigammaTwoShiftFiniteRate (raw raw_rate leftError rightError log_gap_at)
open GaussianHarmonicLogarithmName (sample data nameF)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def window (a b A y : PTm n) : Fm PTm n := le a (y+A*b) ⋏ le y (a+A*b)
def input (a b c d A : PTm n) : Fm PTm n :=
  source a b ⋏ (le one A ⋏ (le ((two*A+one)*b) a ⋏ (window a b A c ⋏ window a b A d)))

def low (b d : PTm n) : PTm n := monus d b
def width (c d : PTm n) : PTm n := monus c d
def coefficient (b A : PTm n) : PTm n := num 4*A*(A+one)*b
def cost (b c d A : PTm n) : PTm n :=
  leftError (low b d) b (width c d) (two*A)+rightError (low b d) b (width c d) (two*A)

ipra_subst window
ipra_subst input [GaussianStirlingGammaLogarithm.source, two]
ipra_subst coefficient

theorem positive_endpoint (a b A y : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le ((two*A+one)*b) a) (hy : Γ ⊢[PRAAx] window a b A y) :
    Γ ⊢[PRAAx] source y b := by
  have hh : Γ ⊢[PRAAx] le b y := by ipra_le sl h + sl hy.andE₁ + 𝔞 A*𝔞 b
  exact .andI (le_trans hb hh) hb

theorem low_split (a b A d : PTm n) (h : Γ ⊢[PRAAx] le ((two*A+one)*b) a)
    (hd : Γ ⊢[PRAAx] window a b A d) :
    Γ ⊢[PRAAx] low b d+b ≐ d := by
  have hh : Γ ⊢[PRAAx] le b d := by ipra_le sl h + sl hd.andE₁ + 𝔞 A*𝔞 b
  exact (add_comm _ _).eqTrans (eq_add_of_le hh).eqSymm

theorem high_split (a b A c d : PTm n) (h : Γ ⊢[PRAAx] le ((two*A+one)*b) a)
    (hd : Γ ⊢[PRAAx] window a b A d) (hDC : Γ ⊢[PRAAx] le d c) :
    Γ ⊢[PRAAx] low b d+b+width c d ≐ c :=
  (congrAdd (low_split a b A d h hd) (.eqRefl _)).eqTrans (eq_add_of_le hDC).eqSymm

private theorem width_le (a b A c d : PTm n)
    (hc : Γ ⊢[PRAAx] window a b A c) (hd : Γ ⊢[PRAAx] window a b A d) :
    Γ ⊢[PRAAx] le (width c d) (two*A*b) := by
  have h : Γ ⊢[PRAAx] le c (d+two*A*b) := by ipra_le sl hc.andE₂ + sl hd.andE₁
  exact le_congr (.eqRefl _) ((congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus _ _))
    (AnalyticNumberTheory.BlockFamily.monus_le_monus (c := d) h)

theorem low_gap (p a b u k : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hu : Γ ⊢[PRAAx] le one u)
    (h3 : Γ ⊢[PRAAx] le a (num 3*u))
    (hA : Γ ⊢[PRAAx] le a (u+k)) (hU : Γ ⊢[PRAAx] le u (a+k)) :
    Γ ⊢[PRAAx] distanceBounded (sample p u b) (sample p a b) (two*k) a := by
  refine .orE (le_total u a) ?_ ?_
  · have h : (le u a :: Γ) ⊢[PRAAx] le u a := Prf.hyp0
    let r := monus a u
    have e : (le u a :: Γ) ⊢[PRAAx] u+r ≐ a := (eq_add_of_le h).eqSymm
    have hR : (le u a :: Γ) ⊢[PRAAx] le r k :=
      le_congr (.eqRefl _) ((congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus _ _))
        (AnalyticNumberTheory.BlockFamily.monus_le_monus (c := u) hA.wk)
    have hT : (le u a :: Γ) ⊢[PRAAx] le (u+r) (num 3*u) := le_congr e.eqSymm (.eqRefl _) h3.wk
    have t := GaussianGammaDigammaTwoShiftTrapezoidGap.trapezoid_gap p u r b k hu.wk hR hT
    exact distance_symmetric _ _ _ _ ha.wk
      (distance_congr (congrAp2 nameF (.eqRefl _) (congrPairT e (.eqRefl _))) (.eqRefl _) (.eqRefl _) e t)
  · have h : (le a u :: Γ) ⊢[PRAAx] le a u := Prf.hyp0
    have h2 : (le a u :: Γ) ⊢[PRAAx] le a (two*u) := by
      ipra_le sl h + Groth.ι (IPRA.Q.mk (le a u :: Γ) u)
    exact log_gap_at p a u b k ha.wk hu.wk h2 hA.wk hU.wk

/-- Compare the logarithm samples at both endpoints of a shift window whose
width bound has numerator `L` on the common denominator `b`. -/
theorem boundary_sample_gaps (p a b c d L : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hL : Γ ⊢[PRAAx] le b L)
    (hbase : Γ ⊢[PRAAx] le (two*L+b) a)
    (hc : Γ ⊢[PRAAx] le a (c+L) ⋏ le c (a+L))
    (hd : Γ ⊢[PRAAx] le a (d+L) ⋏ le d (a+L))
    (hlt : Γ ⊢[PRAAx] lt d c) :
    let u := low b d
    let r := width c d
    let k := two*(L+b)
    Γ ⊢[PRAAx] source u b ⋏ (le one r ⋏
      (distanceBounded (sample p u b) (sample p a b) k a ⋏
       distanceBounded (sample p (u+b+r) b) (sample p a b) k a)) := by
  let u := low b d
  let r := width c d
  let k := L+b
  have b_le_d : Γ ⊢[PRAAx] le b d := by ipra_le sl hbase + sl hd.andE₁ + 𝔞 L
  have ed : Γ ⊢[PRAAx] u+b ≐ d := (add_comm _ _).eqTrans (eq_add_of_le b_le_d).eqSymm
  have ec : Γ ⊢[PRAAx] u+b+r ≐ c :=
    (congrAdd ed (.eqRefl _)).eqTrans (eq_add_of_le (le_of_lt hlt)).eqSymm
  have hUL : Γ ⊢[PRAAx] le a (u+(L+b)) :=
    le_congr (.eqRefl _)
      ((congrAdd ed (.eqRefl L)).eqSymm.eqTrans (by ipra_ring)) hd.andE₁
  have b_le_u : Γ ⊢[PRAAx] le b u := by ipra_le sl hUL + sl hbase + sl hL
  have hU := le_trans hb b_le_u
  have hU3 : Γ ⊢[PRAAx] le a (num 3*u) := by ipra_le 3*sl hUL + 2*sl hbase + sl hL
  have hUH : Γ ⊢[PRAAx] le u (a+k) := by
    have tu : Γ ⊢[PRAAx] le u d := le_congr (.eqRefl _) ed (le_add_right _ _)
    unfold k
    ipra_le sl tu + sl hd.andE₂ + 𝔞 b
  have low := low_gap p a b u k ha hU hU3 hUL hUH
  have b_le_c : Γ ⊢[PRAAx] le b c := by ipra_le sl hbase + sl hc.andE₁ + 𝔞 L
  have hC := le_trans hb b_le_c
  have hC2 : Γ ⊢[PRAAx] le a (two*c) := by ipra_le 2*sl hc.andE₁ + sl hbase + 𝔞 b
  have hCL : Γ ⊢[PRAAx] le a (c+k) := by unfold k; ipra_le sl hc.andE₁ + 𝔞 b
  have hCH : Γ ⊢[PRAAx] le c (a+k) := by unfold k; ipra_le sl hc.andE₂ + 𝔞 b
  have high := log_gap_at p a c b k ha hC hC2 hCL hCH
  have hNear := distance_congr (congrAp2 nameF (.eqRefl _) (congrPairT ec.eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) high
  exact .andI (.andI hU hb) (.andI (Common.one_le_monus_of_lt d c hlt) (.andI low hNear))

theorem numerator_mono (q v E F D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hEF : Γ ⊢[PRAAx] le E F) (h : Γ ⊢[PRAAx] upper q v E D) : Γ ⊢[PRAAx] upper q v F D :=
  upper_mono _ _ _ _ _ _ hD h (le_mul_mono hEF (le_refl _))

theorem forward_raw (p a b c d A : PTm n) (h : Γ ⊢[PRAAx] input a b c d A)
    (hlt : Γ ⊢[PRAAx] lt d c) :
    Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (raw p a (low b d) b (width c d))) (coefficient b A*unit p+cost b c d A*a) (a*unit p) ⋏
       upper (fstT (raw p a (low b d) b (width c d))) (fstT qzero) (coefficient b A*unit p+cost b c d A*a) (a*unit p)) := by
  let u := low b d
  let r := width c d
  let k := A*b+b
  let M := two*A
  have ha := h.andE₁.andE₁
  have hb := h.andE₁.andE₂
  have hA := h.andE₂.andE₁
  have hbase := h.andE₂.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₂.andE₁
  have hd := h.andE₂.andE₂.andE₂.andE₂
  have hL : Γ ⊢[PRAAx] le b (A*b) :=
    le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right b hA)
  have hScaled : Γ ⊢[PRAAx] le (two*(A*b)+b) a :=
    le_congr (by ipra_ring) (.eqRefl _) hbase
  have gaps := boundary_sample_gaps p a b c d (A*b) ha hb hL hScaled hc hd hlt
  have hD := positive_product _ _ ha (unit_positive p)
  have cut := raw_rate p a u b r (two*k) M ha gaps.andE₁ gaps.andE₂.andE₁
    (width_le a b A c d hc hd) gaps.andE₂.andE₂.andE₁ gaps.andE₂.andE₂.andE₂
  refine .andI ?_ ?_
  · exact numerator_mono _ _ _ _ _ hD
      (le_of_eq_add (d := rightError u b r M*a) (by unfold coefficient cost M k u r; ipra_ring)) cut.andE₁
  · exact numerator_mono _ _ _ _ _ hD
      (le_of_eq_add (d := leftError u b r M*a) (by unfold coefficient cost M k u r; ipra_ring)) cut.andE₂

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftWindow
