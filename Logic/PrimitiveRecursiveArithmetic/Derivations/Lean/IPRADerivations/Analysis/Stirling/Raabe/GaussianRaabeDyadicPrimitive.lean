import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeLogPrimitiveCell
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmPower

/-!
# The actual logarithm primitive at a positive dyadic cutoff

The original logarithm of `2^(-h)` has an observation bound linear in
`h`, by the checked logarithm power identity at `1/2`. Multiplying
by the actual rational cutoff gives a vanishing primitive bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 900000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeDyadicPrimitive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianHarmonicLogarithmPower (scaledF scaledData)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianPositiveRationalLogarithm (source data logF sample fraction)
open GaussianRaabeLogPrimitiveCell (primitive fraction_bound)
open GaussianRationalDistanceOrder (distance_symmetric distance_radius_mono distance_congr)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (natScale naturalPoint)
open GaussianRationalReciprocal (bound_congr bounded_product bounded_negative)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data

private theorem common_clock (f g : PR 2) (p x y : PTm n) (h : Γ ⊢[PRAAx] crossEquivalent f g x y) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 g p y) two one := by
  have pos := unit_positive (Γ := Γ) p
  exact distance_radius_mono _ _ _ _ two one (positive_product _ _ pos pos) (le_refl one)
    (by
      let U := unit p
      change Γ ⊢[PRAAx] le ((U+U)*one) (two*(U*U))
      ipra_le 2*Groth.ι (IPRA.Q.mk Γ U)*sl pos)
    (cross_at f g x y p p h)

private theorem harmonic_half_bound (p : PTm n) :
    Γ ⊢[PRAAx] bounded (GaussianHarmonicLogarithmName.sample p one two) (num 31) one := by
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  have hs : Γ ⊢[PRAAx] source one two := .andI (le_refl one) h₂
  have domain : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain one two two one :=
    .andI hs (.andI (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))
      (le_congr (.eqRefl _) (one_mul _).eqSymm h₂))
  have ordinary : Γ ⊢[PRAAx] bounded (sample p one two) (num 29) one :=
    bound_congr (.eqRefl _) (by unfold GaussianCompactLogarithmBounds.radius; ipra_ring) (.eqRefl _)
      (GaussianCompactLogarithmBounds.sample_bound p one two two one h₂ domain)
  have near := common_clock logF H p (data one two) (hd one two)
    (GaussianHarmonicLogarithmName.cross_original one two hs)
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one)
      (distance_symmetric _ _ _ _ (le_refl one) near) ordinary)

theorem log_sample_bound (p h : PTm n) :
    Γ ⊢[PRAAx] bounded (sample p one (unit h)) (num 31*h+two) one := by
  let q := GaussianNamedNaturalScale.clock p h
  let x : PTm n := hd one two
  let S := GaussianHarmonicLogarithmName.sample q one two
  let d := scaledData one two h
  let v := ap2 scaledF p d
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  have raw := GaussianHarmonicLogarithmPower.original_logarithm_power one two h (.andI (le_refl one) h₂)
  have e : Γ ⊢[PRAAx] data (pw one h) (unit h) ≐ data one (unit h) := by
    simpa only [GaussianPositiveRationalLogarithm.subst_data,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (data (var 0) (var 1) : PTm 2)
        (σ := ![pw one h,unit h]) (σ' := ![one,unit h])
        (fun i => by fin_cases i; exact GaussianPolynomialPerturbation.one_power h; exact .eqRefl _)
  have near : Γ ⊢[PRAAx] distanceBounded (sample p one (unit h)) v two one :=
    distance_congr (congrAp2 logF (.eqRefl p) e) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (common_clock logF scaledF p (data (pw one h) (unit h)) d raw)
  have scale : Γ ⊢[PRAAx] v ≐ qmul (naturalPoint h) S :=
    (GaussianNamedNaturalScale.sample_at (Γ := Γ) H p h h x).eqTrans
      (GaussianRationalNaturalScale.natScale_as_product h S)
  have prod : Γ ⊢[PRAAx] bounded v (num 31*h) one :=
    bound_congr scale.eqSymm (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ h one (num 31) one (le_refl one) (le_refl one)
        (fraction_bound h one (le_refl one)) (harmonic_half_bound q))
  exact bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
    (GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ (le_refl one) (le_refl one) near prod)

def cost (h : PTm n) : PTm n := num 31*h+num 3

theorem primitive_bound (p h : PTm n) :
    Γ ⊢[PRAAx] bounded (primitive p one (unit h)) (cost h) (unit h) := by
  let D := unit h
  let x := fraction one D
  let l := sample p one D
  have hD := unit_positive (Γ := Γ) h
  have hx := fraction_bound one D hD
  have product : Γ ⊢[PRAAx] bounded (qmul x l) (num 31*h+two) D :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (bounded_product _ _ _ _ _ _ hD (le_refl one) hx (log_sample_bound p h))
  exact bound_congr (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ hD product (bounded_negative _ _ _ hD hx))

theorem actual_logarithm_primitive_at_positive_dyadic_cutoff_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (bounded (primitive (var 0) one (unit (var 1))) (cost (var 1)) (unit (var 1))) :=
  closeUniv 2 (primitive_bound _ _)

end LeanProofs.IPRA.Analysis.GaussianRaabeDyadicPrimitive
