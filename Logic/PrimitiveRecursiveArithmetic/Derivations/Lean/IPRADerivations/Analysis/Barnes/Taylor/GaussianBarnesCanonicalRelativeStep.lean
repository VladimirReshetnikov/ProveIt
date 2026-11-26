import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalDerivativeRow
import IPRADerivations.Analysis.Logarithm.GaussianLocalLogarithmMultiplicativeIncrement
import IPRADerivations.Analysis.Geometry.GaussianRelativeNormTriangle

/-!
# Actual relative step of the Barnes local logarithm

For common denominator `B*k` and native increment `h`, the relative
argument is `h/(B*k+z)`. Its Gaussian numerator and denominator satisfy
the local Mercator source and certify the exact multiplicative increment.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (add mul scale normSq normSq_mul normSq_eval oneCode)
open GaussianBarnesCanonicalFactor (base)
open GaussianBarnesCanonicalLogRow (local_source)
open GaussianGammaEulerHeadLower (translated)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical positive_product
  canonical_unique qadd qadd_canonical qadd_represents qmul qmul_canonical qmul_represents
  represents_congr represents_rescale)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (conjugate norm_conjugate qone qone_represents_scaled re_conjugate im_conjugate)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_mul im_mul re_scale im_scale re_one im_one)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "rowSource" => GaussianBarnesCanonicalLogRow.source
local notation "nativeBound" => ComplexLogarithmRemainder.bounded
local notation "L" => GaussianLocalLogarithmName.pointF
local notation "ld" => GaussianLocalLogarithmName.data

def source (z h R B k H : PTm n) : Fm PTm n := rowSource z R B k ⋏
  (rowSource (add z h) R B k ⋏ (nativeBound h H ⋏ le (num 16*H) (B*k)))

def numerator (z h B k : PTm n) : PTm n := mul h (conjugate (translated z B k))
def denominator (z B k : PTm n) : PTm n := normSq (translated z B k)
def radius (H B k : PTm n) : PTm n := (two*H)*(B*k)
def relative (z h B k : PTm n) : PTm n := ofGaussian (numerator z h B k) (denominator z B k)

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z h R B k H : PTm n) :
    (source z h R B k H).subst σ =
      source (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) (Syn.subst σ H) := by
  simp [source,ComplexLogarithmRemainder.bounded]

@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (numerator z h B k) = numerator (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [numerator]

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (z B k : PTm n) :
    Syn.subst σ (denominator z B k) = denominator (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ k) := by simp [denominator]

@[simp] theorem subst_radius {m : ℕ} (σ : Fin n → PTm m) (H B k : PTm n) :
    Syn.subst σ (radius H B k) = radius (Syn.subst σ H) (Syn.subst σ B) (Syn.subst σ k) := by simp [radius,two]

@[simp] theorem subst_relative {m : ℕ} (σ : Fin n → PTm m) (z h B k : PTm n) :
    Syn.subst σ (relative z h B k) = relative (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ B) (Syn.subst σ k) := by simp [relative]

theorem reciprocal_margin (z R B k : PTm n) (h : Γ ⊢[PRAAx] rowSource z R B k) :
    Γ ⊢[PRAAx] le ((B*k)*(B*k)) (num 4*denominator z B k) := by
  let d := B*k
  have hB := h.andE₁
  have hk := h.andE₂.andE₁
  have hd := positive_product B k hB hk
  have clear := GaussianRationalLowerBounds.lower_to_cleared (base z B k) (translated z B k) d one two hd
    (zero_lt_succ one) (GaussianBarnesCanonicalBase.base_represents z B k hB hk)
    (GaussianBarnesCanonicalDerivativeRow.base_lower z R B k h)
  exact le_congr (by dsimp only [d]; ipra_ring) (by unfold denominator; ipra_ring) clear

theorem denominator_positive (z R B k : PTm n) (h : Γ ⊢[PRAAx] rowSource z R B k) :
    Γ ⊢[PRAAx] le one (denominator z B k) := by
  let d := B*k
  let E := denominator z B k
  have hd := positive_product B k h.andE₁ h.andE₂.andE₁
  have nz := le_trans (positive_product d d hd hd) (reciprocal_margin z R B k h)
  refine (zero_or_succ E).orE ?_ ?_
  · have e : (E ≐ zero) :: Γ ⊢[PRAAx] E ≐ zero := Prf.hyp0
    exact not_succ_le_self zero _ (le_congr (.eqRefl _) ((congrMul (.eqRefl _) e).eqTrans (mul_zero _)) nz.wk)
  · have e : (E ≐ ConciseIPRA.PTm.succ (pred E)) :: Γ ⊢[PRAAx] E ≐ ConciseIPRA.PTm.succ (pred E) := Prf.hyp0
    exact le_congr (.eqRefl _) e.eqSymm (zero_lt_succ _)

private theorem translated_bound (z R B k : PTm n) (h : Γ ⊢[PRAAx] rowSource z R B k) :
    Γ ⊢[PRAAx] nativeBound (translated z B k) (two*(B*k)) := by
  let d := B*k
  let T := R*B
  let q := scale d oneCode
  have h0 : Γ ⊢[PRAAx] nativeBound oneCode one :=
    le_congr ComplexLogarithmRemainder.normSq_one.eqSymm (by ipra_ring) (le_refl one)
  have hq : Γ ⊢[PRAAx] le (normSq q) (d*d*one) :=
    le_congr (.eqRefl _) (by ipra_ring) (ComplexLogarithmRemainder.bounded_scale d h0)
  have hz : Γ ⊢[PRAAx] le (normSq z) (T*T*one) :=
    le_congr (.eqRefl _) (by dsimp only [T]; ipra_ring) h.andE₂.andE₂.andE₁
  have big := GaussianRelativeNormTriangle.relative_triangle z q T d one hz hq
  have led : Γ ⊢[PRAAx] le T d :=
    le_congr (.eqRefl _) (mul_comm _ _) (mul_le_mul_right B
      (le_trans (le_of_eq_add (d := R) (by ipra_ring)) h.andE₂.andE₂.andE₂))
  have cap : Γ ⊢[PRAAx] le (T+d) (two*d) :=
    le_congr (.eqRefl _) (by ipra_ring) (add_le_add₂ led (le_refl d))
  exact le_trans (le_congr (.eqRefl _) (by ipra_ring) big) (le_mul_mono cap cap)

private theorem numerator_norm (z h B k H : PTm n) (hh : Γ ⊢[PRAAx] nativeBound h H) :
    Γ ⊢[PRAAx] le (normSq (numerator z h B k)) (H*H*denominator z B k) :=
  le_congr ((normSq_mul _ _).eqTrans (congrMul (.eqRefl _) (norm_conjugate _))).eqSymm (.eqRefl _)
    (mul_le_mul_right (denominator z B k) hh)

theorem relative_bound (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] bounded (relative z h B k) (two*H) (B*k) := by
  let d := B*k
  let E := denominator z B k
  let a := numerator z h B k
  have hd := positive_product B k hs.andE₁.andE₁ hs.andE₁.andE₂.andE₁
  have hE := denominator_positive z R B k hs.andE₁
  have margin := reciprocal_margin z R B k hs.andE₁
  have bound := le_mul_mono margin (numerator_norm z h B k H hs.andE₂.andE₂.andE₁)
  exact bounded_of_cleared _ _ _ _ _ hE hd (ofGaussian_represents a E hE)
    (le_congr (.eqRefl _) (by ipra_ring) bound)

theorem local_admission (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source (numerator z h B k) (radius H B k) (denominator z B k) := by
  let d := B*k
  let E := denominator z B k
  let a := translated z B k
  let T := radius H B k
  have bound := translated_bound z R B k hs.andE₁
  have conj : Γ ⊢[PRAAx] nativeBound (conjugate a) (two*d) :=
    le_congr (norm_conjugate a).eqSymm (.eqRefl _) bound
  have norm := ComplexLogarithmRemainder.bounded_mul hs.andE₂.andE₂.andE₁ conj
  have hd := reciprocal_margin z R B k hs.andE₁
  have fit : Γ ⊢[PRAAx] le (num 4*(two*T)) (num 4*E) :=
    le_trans (le_congr (by unfold T radius d; ipra_ring) (.eqRefl _) (mul_le_mul_right d hs.andE₂.andE₂.andE₂)) hd
  have positive : Γ ⊢[PRAAx] le one (num 4 : PTm n) := le_of_eq_add (d := num 3) (by ipra_ring)
  exact .andI (denominator_positive z R B k hs.andE₁)
    (.andI (le_congr (.eqRefl _) (by simp only [radius,d]; ipra_ring) norm)
      (LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep.cancel_pos positive fit))

private theorem native_product_identity (z h B k : PTm n) :
    let a := translated z B k
    let E := denominator z B k
    Γ ⊢[PRAAx] equal (mul a (add (scale E oneCode) (numerator z h B k))) (scale E (translated (add z h) B k)) := by
  dsimp only
  apply equal_of_values <;>
    simp only [numerator,re_mul,im_mul,re_add,im_add,re_scale,im_scale,re_conjugate,im_conjugate,re_one,im_one,
      denominator,normSq_eval,translated] <;> ring

theorem product_identity (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] qmul (base z B k) (qadd qone (relative z h B k)) ≐ base (add z h) B k := by
  let a := translated z B k
  let b := translated (add z h) B k
  let d := B*k
  let E := denominator z B k
  let x := numerator z h B k
  let u := base z B k
  let v := base (add z h) B k
  let Q := qadd qone (relative z h B k)
  have hB := hs.andE₁.andE₁
  have hk := hs.andE₁.andE₂.andE₁
  have hd := positive_product B k hB hk
  have hE := denominator_positive z R B k hs.andE₁
  have qa := GaussianBarnesCanonicalBase.base_represents z B k hB hk
  have qb := GaussianBarnesCanonicalBase.base_represents (add z h) B k hB hk
  have reQ := qadd_represents qone (relative z h B k) (scale E oneCode) x E hE
    (qone_represents_scaled E) (ofGaussian_represents x E hE)
  have raw := qmul_represents u Q a (add (scale E oneCode) x) d E hd hE qa reQ
  exact canonical_unique (qmul u Q) v (scale E b) (d*E) (qmul_canonical _ _) (qadd_canonical _ _)
    (positive_product d E hd hE) (represents_congr (.eqRefl _) (native_product_identity z h B k) (.eqRefl _) raw)
    (represents_rescale v b d E qb)

theorem logarithm_increment (z h R B k H : PTm n) (hs : Γ ⊢[PRAAx] source z h R B k H) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedDifference.nameF L L) L
      (GaussianNamedDifference.data (ld (add z h) (R*B) (B*k)) (ld z (R*B) (B*k)))
      (ld (numerator z h B k) (radius H B k) (denominator z B k)) :=
  GaussianLocalLogarithmMultiplicativeIncrement.increment_cross z (R*B) (B*k)
    (numerator z h B k) (radius H B k) (denominator z B k) (add z h) (R*B) (B*k)
    (local_source z R B k hs.andE₁) (local_admission z h R B k H hs)
    (local_source (add z h) R B k hs.andE₂.andE₁) (product_identity z h R B k H hs)

theorem actual_relative_Barnes_Mercator_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let k := var 4
     let H := var 5
     source z h R B k H ⟶ crossEquivalent (GaussianNamedDifference.nameF L L) L
       (GaussianNamedDifference.data (ld (add z h) (R*B) (B*k)) (ld z (R*B) (B*k)))
       (ld (numerator z h B k) (radius H B k) (denominator z B k))) :=
  closeUniv 6 (.impI (logarithm_increment _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalRelativeStep
