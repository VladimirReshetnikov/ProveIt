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

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaDigammaTwoShiftFiniteRate (raw raw_rate leftError rightError log_gap_at)
open GaussianHarmonicLogarithmName (sample data nameF)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianStirlingGammaLogarithm (source)
open RationalValueBounds (upper upper_mono)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num monus)

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

@[simp] theorem subst_window {m : ℕ} (σ : Fin n → PTm m) (a b A y : PTm n) :
    (window a b A y).subst σ = window (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ A) (Syn.subst σ y) := by simp [window]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (a b c d A : PTm n) :
    (input a b c d A).subst σ = input (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ A) := by
  simp [input,GaussianStirlingGammaLogarithm.source,two]
@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (b A : PTm n) :
    Syn.subst σ (coefficient b A) = coefficient (Syn.subst σ b) (Syn.subst σ A) := by simp [coefficient]

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
  let k := (A+one)*b
  let M := two*A
  have ha := h.andE₁.andE₁
  have hb := h.andE₁.andE₂
  have hA := h.andE₂.andE₁
  have hbase := h.andE₂.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₂.andE₁
  have hd := h.andE₂.andE₂.andE₂.andE₂
  have ed := low_split a b A d hbase hd
  have ec := high_split a b A c d hbase hd (le_of_lt hlt)
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
    ipra_le sl hUL + sl hbase + 𝔞 b*sl hA
  have hU3 : Γ ⊢[PRAAx] le a (num 3*u) := by
    unfold k at hUL
    ipra_le 3*sl hUL + 2*sl hbase + 𝔞 b*sl hA
  have hUH : Γ ⊢[PRAAx] le u (a+k) := by
    have tu : Γ ⊢[PRAAx] le u d := le_congr (.eqRefl _) ed (le_add_right _ _)
    unfold k
    ipra_le sl tu + sl hd.andE₂ + 𝔞 b
  have low := low_gap p a b u k ha hU hU3 hUL hUH
  have hC := (positive_endpoint a b A c hb hbase hc).andE₁
  have hC2 : Γ ⊢[PRAAx] le a (two*c) := by ipra_le 2*sl hc.andE₁ + sl hbase + 𝔞 b
  have hCL : Γ ⊢[PRAAx] le a (c+k) := by unfold k; ipra_le sl hc.andE₁ + 𝔞 b
  have hCH : Γ ⊢[PRAAx] le c (a+k) := by unfold k; ipra_le sl hc.andE₂ + 𝔞 b
  have high := log_gap_at p a c b k ha hC hC2 hCL hCH
  have hNear := distance_congr (congrAp2 nameF (.eqRefl _) (congrPairT ec.eqSymm (.eqRefl _)))
    (.eqRefl _) (.eqRefl _) (.eqRefl _) high
  have hr : Γ ⊢[PRAAx] le one r := by
    have e := natEq (eq_add_of_le (le_of_lt hlt))
    unfold r width
    ipra_le sl hlt with -e
  have hD := positive_product _ _ ha (unit_positive p)
  have cut := raw_rate p a u b r (two*k) M ha (.andI hU hb) hr (width_le a b A c d hc hd) low hNear
  refine .andI ?_ ?_
  · exact numerator_mono _ _ _ _ _ hD
      (le_of_eq_add (d := rightError u b r M*a) (by unfold coefficient cost M k u r; ipra_ring)) cut.andE₁
  · exact numerator_mono _ _ _ _ _ hD
      (le_of_eq_add (d := leftError u b r M*a) (by unfold coefficient cost M k u r; ipra_ring)) cut.andE₂

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftWindow
