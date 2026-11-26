import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftExactFiniteRate
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftWindow

/-!
# The exact rational shift window for the original Gamma secants

The bound is L/b on the same rational chart as the original base a/b
and shifted arguments. The finite rate retains the leading rational
constant 4L(L+b)/(a·b).
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRationalWindow

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaDigammaTwoShiftExactFiniteRate (raw_rate leftSlack rightSlack)
open GaussianGammaDigammaTwoShiftFiniteRate (raw log_gap_at)
open GaussianGammaDigammaTwoShiftWindow (low width numerator_mono)
open GaussianHarmonicLogarithmName (sample data nameF)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def window (a L y : PTm n) : Fm PTm n := le a (y+L) ⋏ le y (a+L)

def input (a b c d L : PTm n) : Fm PTm n :=
  source a b ⋏ (le b L ⋏ (le (two*L+b) a ⋏ (window a L c ⋏ window a L d)))

def coefficient (b L : PTm n) : PTm n := num 4*L*(L+b)

def cost (b c d : PTm n) : PTm n :=
  leftSlack (low b d) b (width c d)+rightSlack (low b d) b (width c d)

ipra_subst window

ipra_subst input [GaussianStirlingGammaLogarithm.source, two]

ipra_subst coefficient

ipra_subst cost [low, width]

theorem positive_endpoint (a b L y : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le (two*L+b) a) (hy : Γ ⊢[PRAAx] window a L y) :
    Γ ⊢[PRAAx] source y b := by
  have hh : Γ ⊢[PRAAx] le b y := by ipra_le sl h + sl hy.andE₁ + 𝔞 L
  exact .andI (le_trans hb hh) hb

theorem low_split (a b L d : PTm n) (h : Γ ⊢[PRAAx] le (two*L+b) a)
    (hd : Γ ⊢[PRAAx] window a L d) :
    Γ ⊢[PRAAx] low b d+b ≐ d := by
  have hh : Γ ⊢[PRAAx] le b d := by ipra_le sl h + sl hd.andE₁ + 𝔞 L
  exact (add_comm _ _).eqTrans (eq_add_of_le hh).eqSymm

theorem high_split (a b L c d : PTm n) (h : Γ ⊢[PRAAx] le (two*L+b) a)
    (hd : Γ ⊢[PRAAx] window a L d) (hDC : Γ ⊢[PRAAx] le d c) :
    Γ ⊢[PRAAx] low b d+b+width c d ≐ c :=
  (congrAdd (low_split a b L d h hd) (.eqRefl _)).eqTrans (eq_add_of_le hDC).eqSymm

theorem width_le (a L c d : PTm n)
    (hc : Γ ⊢[PRAAx] window a L c) (hd : Γ ⊢[PRAAx] window a L d) :
    Γ ⊢[PRAAx] le (width c d) (two*L) := by
  have h : Γ ⊢[PRAAx] le c (d+two*L) := by ipra_le sl hc.andE₂ + sl hd.andE₁
  exact le_congr (.eqRefl _) ((congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus _ _))
    (AnalyticNumberTheory.BlockFamily.monus_le_monus (c := d) h)

private theorem low_gap (p a b u k : PTm n)
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

theorem forward_raw (p a b c d L : PTm n) (h : Γ ⊢[PRAAx] input a b c d L)
    (hlt : Γ ⊢[PRAAx] lt d c) : Γ ⊢[PRAAx]
      (upper (fstT qzero) (fstT (raw p a (low b d) b (width c d)))
        (coefficient b L*unit p+cost b c d*(a*b)) ((a*b)*unit p) ⋏
       upper (fstT (raw p a (low b d) b (width c d))) (fstT qzero)
        (coefficient b L*unit p+cost b c d*(a*b)) ((a*b)*unit p)) := by
  let u := low b d
  let r := width c d
  let k := L+b
  let U := unit p
  have ha := h.andE₁.andE₁
  have hb := h.andE₁.andE₂
  have hL := h.andE₂.andE₁
  have hbase := h.andE₂.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₂.andE₁
  have hd := h.andE₂.andE₂.andE₂.andE₂
  have ed := low_split a b L d hbase hd
  have ec := high_split a b L c d hbase hd (le_of_lt hlt)
  have hUL : Γ ⊢[PRAAx] le a (u+k) :=
    le_congr (.eqRefl _) (by
      have e := natEq ed
      unfold k
      apply deriveNat
      ipra_simps
      linear_combination -e) hd.andE₁
  have hU : Γ ⊢[PRAAx] le one u := by
    refine le_trans hb ?_
    unfold k at hUL
    ipra_le sl hUL+sl hbase+sl hL
  have hU3 : Γ ⊢[PRAAx] le a (num 3*u) := by
    unfold k at hUL
    ipra_le 3*sl hUL+2*sl hbase+sl hL
  have hUH : Γ ⊢[PRAAx] le u (a+k) := by
    have tu : Γ ⊢[PRAAx] le u d := le_congr (.eqRefl _) ed (le_add_right _ _)
    unfold k
    ipra_le sl tu+sl hd.andE₂+𝔞 b
  have low := low_gap p a b u k ha hU hU3 hUL hUH
  have hC := (positive_endpoint a b L c hb hbase hc).andE₁
  have hC2 : Γ ⊢[PRAAx] le a (two*c) := by ipra_le 2*sl hc.andE₁+sl hbase+𝔞 b
  have hCL : Γ ⊢[PRAAx] le a (c+k) := by unfold k; ipra_le sl hc.andE₁+𝔞 b
  have hCH : Γ ⊢[PRAAx] le c (a+k) := by unfold k; ipra_le sl hc.andE₂+𝔞 b
  have high := log_gap_at p a c b k ha hC hC2 hCL hCH
  have hNear := distance_congr (congrAp2 nameF (.eqRefl _) (congrPairT ec.eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) high
  have hr : Γ ⊢[PRAAx] le one r := by
    have e := natEq (eq_add_of_le (le_of_lt hlt))
    unfold r width
    ipra_le sl hlt with -e
  have hD := positive_product _ _ (positive_product _ _ ha hb) (unit_positive p)
  have wr : Γ ⊢[PRAAx] le r (two*L) := width_le a L c d hc hd
  have major : Γ ⊢[PRAAx] le (r*(two*k)*U) (coefficient b L*U) := by
    dsimp only [coefficient,k]
    ipra_le 2*𝔞(L+b)*𝔞(U)*sl wr
  have ls : Γ ⊢[PRAAx] le (leftSlack u b r*a) (cost b c d*(a*b)) := by
    dsimp only [cost]
    ipra_le 𝔞(leftSlack u b r)*𝔞(a)*sl hb+𝔞(rightSlack u b r)*𝔞(a)*𝔞(b)
  have rs : Γ ⊢[PRAAx] le (rightSlack u b r*a) (cost b c d*(a*b)) := by
    dsimp only [cost]
    ipra_le 𝔞(rightSlack u b r)*𝔞(a)*sl hb+𝔞(leftSlack u b r)*𝔞(a)*𝔞(b)
  have cut := raw_rate p a u b r (two*k) ha (.andI hU hb) hr low hNear
  exact .andI (numerator_mono _ _ _ _ _ hD (add_le_add₂ major ls) cut.andE₁)
    (numerator_mono _ _ _ _ _ hD (add_le_add₂ major rs) cut.andE₂)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRationalWindow
