import IPRADerivations.Analysis.Names.LogisticName
import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumIntervals
import IPRADerivations.Analysis.RationalArithmetic.Grids.RationalCubeMidpoint

/-!
# The clipped rational parameter of the arctangent extension

Clipping is performed on the decoded signed numerator over the actual
positive denominator. It contracts rational distance, and it preserves
the represented value throughout the closed unit interval.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentClippedParameter

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (le_add_ad)
open LogisticName (clip)
open RationalArithmetic (represents)
open RationalCubeMidpoint (fraction fraction_represents)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (upper radius radius_of_upper cross_absolute)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def denominator (s : PTm n) : PTm n := denominatorOf s
def numerator (s : PTm n) : PTm n := clip (numeratorOf s).pos (numeratorOf s).neg (denominator s)
def value (s : PTm n) : PTm n := fraction (numerator s) (denominator s)

@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (denominator s) = denominator (Syn.subst σ s) := by
  simp [denominator,denominatorOf]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (s : PTm n) :
    Syn.subst σ (numerator s) = numerator (Syn.subst σ s) := by
  simp [numerator,numeratorOf,ZT.subst]

theorem denominator_positive (s : PTm n) : Γ ⊢[PRAAx] le one (denominator s) :=
  RationalArgmin.denominator_positive s
theorem numerator_le (s : PTm n) : Γ ⊢[PRAAx] le (numerator s) (denominator s) :=
  LogisticName.clip_range _ _ _

private theorem fraction_upper (a b c d H K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (K*ad (a*d) (c*b)) (H*b*d)) :
    Γ ⊢[PRAAx] upper (fraction a b) (fraction c d) H K := by
  have h' : Γ ⊢[PRAAx] le (K*(a*d)) (K*(c*b)+H*b*d) :=
    le_trans (le_congr (.eqRefl _) (by ipra_ring)
      (le_mul_mono (le_refl K) (le_add_ad (a*d) (c*b))))
      (add_le_add₂ (le_refl _) h)
  have e := natEq (eq_add_of_le h')
  apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat a) (ZT.ofNat c) b d H K hb hd
    (fraction_represents _ _ hb) (fraction_represents _ _ hd)
  apply zle_of_toZ (monus (K*(c*b)+H*b*d) (K*(a*d)))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,ZT.toZ_sub]
  ipra_simps
  linear_combination -e

theorem radius_of_cleared (a b c d H K : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] le (K*ad (a*d) (c*b)) (H*b*d)) :
    Γ ⊢[PRAAx] radius (fraction a b) (fraction c d) H K := by
  have swap : Γ ⊢[PRAAx] ad (a*d) (c*b) ≐ ad (c*b) (a*d) := add_comm _ _
  exact radius_of_upper _ _ _ _ (fraction_upper a b c d H K hb hd h)
    (fraction_upper c d a b H K hd hb (le_congr (congrMul (.eqRefl K) swap) (by ipra_ring) h))

theorem value_radius (a b H K : PTm n) (h : Γ ⊢[PRAAx] radius a b H K) :
    Γ ⊢[PRAAx] radius (value a) (value b) H K := by
  have clipBound := LogisticName.clip_rational (Γ := Γ) (numeratorOf a).pos (numeratorOf a).neg (denominator a)
    (numeratorOf b).pos (numeratorOf b).neg (denominator b)
  have native := le_congr (congrMul (.eqRefl K) (cross_absolute a b)) (.eqRefl _) h
  exact radius_of_cleared _ _ _ _ H K (denominator_positive a) (denominator_positive b)
    (le_trans (le_mul_mono (le_refl K) clipBound) native)

theorem representation_clips_exactly (s A B : PTm n)
    (hA : Γ ⊢[PRAAx] le A B) (hrep : Γ ⊢[PRAAx] represents s (ZT.ofNat A) B) :
    Γ ⊢[PRAAx] numerator s*B ≐ A*denominator s := by
  let p := (numeratorOf s).pos
  let q := (numeratorOf s).neg
  let D := denominator s
  have read : Γ ⊢[PRAAx] B*p ≐ A*D+B*q := by
    have e := ZT.toZ_eq hrep
    apply deriveNat
    simp only [RationalArithmetic.represents,ZT.toZ_mul,ZT.toZ_ofNat] at e
    simp only [ZT.toZ] at e
    dsimp only [p,q,D,denominator]
    ipra_simps
    linear_combination -e
  have difference : Γ ⊢[PRAAx] monus (B*p) (B*q) ≐ A*D :=
    (congrMonus read (.eqRefl _)).eqTrans (add_monus _ _)
  have inRange : Γ ⊢[PRAAx] le (monus (B*p) (B*q)) (B*D) :=
    le_congr difference.eqSymm (.eqRefl _) (le_mul_mono hA (le_refl D))
  exact (mul_comm _ _).eqTrans
    ((LogisticName.clip_scale p q D B).eqSymm.eqTrans ((LogisticName.clip_middle inRange).eqTrans difference))

theorem actual_arctangent_clipped_parameter_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (radius (var 0) (var 1) (var 2) (var 3) ⟶ radius (value (var 0)) (value (var 1)) (var 2) (var 3)) :=
  closeUniv 4 (.impI (value_radius _ _ _ _ Prf.hyp0))

theorem actual_arctangent_clipped_parameter_specialization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 1) (var 2) ⟶ represents (var 0) (ZT.ofNat (var 1)) (var 2) ⟶
      numerator (var 0)*var 2 ≐ var 1*denominator (var 0)) :=
  closeUniv 3 (.impI (.impI (representation_clips_exactly _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentClippedParameter
