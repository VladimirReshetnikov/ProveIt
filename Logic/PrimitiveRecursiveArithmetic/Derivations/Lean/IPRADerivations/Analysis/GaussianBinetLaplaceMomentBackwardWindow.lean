import IPRADerivations.Analysis.GaussianBinetLaplaceMomentRescale
import IPRADerivations.Analysis.GaussianBinetLaplaceMomentMarginBound

/-!
# A fixed-base backward window for the original Binet moments

A positive rational displacement of at most 1/(2D) leaves X/D-h
in the fixed positive margin 1/(2D). Apply the forward Taylor
comparison there, then return its right endpoint to the original
X/D evaluator by actual rational chart invariance.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentBackwardWindow

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBinetLaplaceMomentImproper (nameF data)
open GaussianBinetLaplaceMomentImproperTaylor (linearSample observation_taylor_with_cap)
open GaussianBinetLaplaceMomentMarginBound (marginBound)
open GaussianBinetLaplaceMomentRescale (rational_proper)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualRadius (radius source_of_right_half_plane)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num monus)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (LeanProofs.IPRA.Q.mk _ t)
local notation "realSource" => GaussianLogGammaEulerResidualDomain.source

def lowerNumerator (X D H Q : PTm n) : PTm n := monus (X*Q) (H*D)

def lowerData (j X D H Q : PTm n) : PTm n :=
  data j (lowerNumerator X D H Q) (D*Q) (radius (lowerNumerator X D H Q) zero)

def source (X D R H Q : PTm n) : Fm PTm n :=
  realSource X zero D zero R ⋏ (le one H ⋏ (le one Q ⋏ le (two*(H*D)) Q))

def secondCap (j D : PTm n) : PTm n := marginBound (succ (succ j)) (two*D)

@[simp] theorem subst_lowerNumerator {m : ℕ} (σ : Fin n → PTm m) (X D H Q : PTm n) :
    Syn.subst σ (lowerNumerator X D H Q) = lowerNumerator (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [lowerNumerator]

@[simp] theorem subst_lowerData {m : ℕ} (σ : Fin n → PTm m) (j X D H Q : PTm n) :
    Syn.subst σ (lowerData j X D H Q) =
      lowerData (Syn.subst σ j) (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [lowerData]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (X D R H Q : PTm n) :
    (source X D R H Q).subst σ = source (Syn.subst σ X) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ H) (Syn.subst σ Q) := by
  simp [source,two,one]

@[simp] theorem subst_secondCap {m : ℕ} (σ : Fin n → PTm m) (j D : PTm n) :
    Syn.subst σ (secondCap j D) = secondCap (Syn.subst σ j) (Syn.subst σ D) := by
  simp [secondCap,two,one]

theorem window_geometry (X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    let Y := lowerNumerator X D H Q
    Γ ⊢[PRAAx] (Y+H*D ≐ X*Q) ⋏ (le one Y ⋏ (le Q (two*Y) ⋏ le H Q)) := by
  let A := H*D
  let Y := lowerNumerator X D H Q
  have hX := h.andE₁.andE₁.andE₁.andE₁
  have hD := h.andE₁.andE₁.andE₂
  have hH := h.andE₂.andE₁
  have hSmall := h.andE₂.andE₂.andE₂
  have hA := positive_product _ _ hH hD
  have hXQ : Γ ⊢[PRAAx] le Q (X*Q) :=
    le_congr (one_mul Q) (.eqRefl _) (le_mul_mono hX (le_refl Q))
  have first : Γ ⊢[PRAAx] le A (two*A) := le_congr (.eqRefl _) (by ipra_ring) (le_add_right A A)
  have below : Γ ⊢[PRAAx] le A (X*Q) := le_trans first (le_trans hSmall hXQ)
  have e : Γ ⊢[PRAAx] Y+A ≐ X*Q := (add_comm Y A).eqTrans (eq_add_of_le below).eqSymm
  have room : Γ ⊢[PRAAx] le (one+A) (two*A) :=
    le_congr (.eqRefl _) (by dsimp only [A]; ipra_ring) (add_le_add₂ hA (le_refl A))
  have hY : Γ ⊢[PRAAx] le one Y := le_of_add_le_add_right (c := A)
    (le_congr (.eqRefl _) e.eqSymm (le_trans room (le_trans hSmall hXQ)))
  have doubles : Γ ⊢[PRAAx] le (Q+two*A) (two*(X*Q)) :=
    le_trans (add_le_add₂ (le_refl Q) hSmall)
      (le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl two) hXQ))
  have margin : Γ ⊢[PRAAx] le Q (two*Y) :=
    le_of_add_le_add_right (c := two*A)
      (le_congr (.eqRefl _) ((congrMul (.eqRefl two) e.eqSymm).eqTrans (by ipra_ring)) doubles)
  have Hbound : Γ ⊢[PRAAx] le H A :=
    le_congr (by ipra_ring) (.eqRefl _) (le_mul_mono (le_refl H) hD)
  exact .andI e (.andI hY (.andI margin (le_trans Hbound (le_trans first hSmall))))

theorem lower_source (X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    let Y := lowerNumerator X D H Q
    Γ ⊢[PRAAx] realSource Y zero (D*Q) zero (radius Y zero) :=
  source_of_right_half_plane _ _ _ _
    (.andI (.andI (window_geometry X D R H Q h).andE₂.andE₁ (.orI₁ (.eqRefl zero)))
      (positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₂.andE₁))

theorem lower_margin (X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] le (D*Q) ((two*D)*lowerNumerator X D H Q) :=
  le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono (le_refl D) (window_geometry X D R H Q h).andE₂.andE₂.andE₁)

theorem margin_positive (X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] le one (two*D) :=
  positive_product _ _ (le_succ_self one) h.andE₁.andE₁.andE₂

theorem lower_observation_bound (p j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] GaussianRationalMetric.bounded (ap2 nameF p (lowerData j X D H Q)) (marginBound j (two*D)) one :=
  GaussianBinetLaplaceMomentMarginBound.observation_bound p j _ _ _ (two*D) (lower_source X D R H Q h)
    (margin_positive X D R H Q h) (lower_margin X D R H Q h)

theorem shifted_source (X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    let Y := lowerNumerator X D H Q
    let E := D*Q
    let A := Y*Q+H*E
    Γ ⊢[PRAAx] realSource A zero (E*Q) zero (radius A zero) := by
  have hY := (window_geometry X D R H Q h).andE₂.andE₁
  have hQ := h.andE₂.andE₂.andE₁
  have hE := positive_product _ _ h.andE₁.andE₁.andE₂ hQ
  exact source_of_right_half_plane _ _ _ _
    (.andI (.andI (le_trans (positive_product _ _ hY hQ) (le_add_right _ _)) (.orI₁ (.eqRefl zero)))
      (positive_product _ _ hE hQ))

theorem shifted_agreement (j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    let Y := lowerNumerator X D H Q
    let E := D*Q
    let A := Y*Q+H*E
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent nameF nameF
      (data j X D R) (data j A (E*Q) (radius A zero)) := by
  apply rational_proper _ _ _ _ _ _ _ h.andE₁ (shifted_source X D R H Q h)
  have add := natEq (window_geometry X D R H Q h).andE₁
  apply deriveNat
  ipra_simps
  linear_combination -𝔞(D)*𝔞(Q)*add

theorem backward_window_taylor (p j X D R H Q : PTm n) (h : Γ ⊢[PRAAx] source X D R H Q) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R))
      (linearSample p j (lowerNumerator X D H Q) (D*Q) (radius (lowerNumerator X D H Q) zero) H Q)
      (num 3*(H*H)*(secondCap j D+num 3)*unit p+num 12*(Q*Q)) ((Q*Q)*unit p) := by
  let Y := lowerNumerator X D H Q
  let E := D*Q
  let A := Y*Q+H*E
  let U := unit p
  have hQ := h.andE₂.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have den := positive_product _ _ (positive_product _ _ hQ hQ) hp
  have cross := GaussianNameEquivalence.cross_at nameF nameF
    (data j X D R) (data j A (E*Q) (radius A zero)) p p (shifted_agreement j X D R H Q h)
  have observations : Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data j X D R))
      (ap2 nameF p (data j A (E*Q) (radius A zero))) (two*(Q*Q)) ((Q*Q)*U) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hp hp) den
      (le_of_eq_add (d := zero) (by dsimp only [U]; ipra_ring)) cross
  have localTaylor := observation_taylor_with_cap p j Y E (radius Y zero) (radius A zero) H Q (secondCap j D)
    (lower_source X D R H Q h) (shifted_source X D R H Q h) hQ
    (window_geometry X D R H Q h).andE₂.andE₂.andE₂
    (lower_observation_bound p (succ (succ j)) X D R H Q h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den observations localTaylor)

theorem actual_improper_Binet_moment_backward_window_Taylor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let p := var 0
     let j := var 1
     let X := var 2
     let D := var 3
     let R := var 4
     let H := var 5
     let Q := var 6
     source X D R H Q ⟶ distanceBounded (ap2 nameF p (data j X D R))
      (linearSample p j (lowerNumerator X D H Q) (D*Q) (radius (lowerNumerator X D H Q) zero) H Q)
      (num 3*(H*H)*(secondCap j D+num 3)*unit p+num 12*(Q*Q)) ((Q*Q)*unit p)) :=
  closeUniv 7 (.impI (backward_window_taylor _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceMomentBackwardWindow
