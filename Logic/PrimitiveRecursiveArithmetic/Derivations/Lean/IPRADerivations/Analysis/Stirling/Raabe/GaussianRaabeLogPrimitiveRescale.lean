import IPRADerivations.Analysis.Stirling.Raabe.GaussianRaabeLogPrimitiveCell

/-!
# Rational representation of the logarithm primitive

At equal positive rational arguments the primitive has exactly the
same underlying value. Independent original sample clocks contribute
only their dyadic allowances multiplied by the argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeLogPrimitiveRescale

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_at)
open GaussianPositiveRationalLogarithm (data fraction logF sample source)
open GaussianRaabeLogPrimitiveCell (fraction_bound primitive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem equal_ratio (p q A B C D : PTm n) (hA : Γ ⊢[PRAAx] source A B)
    (hC : Γ ⊢[PRAAx] source C D) (h : Γ ⊢[PRAAx] A*D ≐ B*C) :
    Γ ⊢[PRAAx] distanceBounded (primitive p A B) (primitive q C D)
      (A*(unit p+unit q)) (B*(unit p*unit q)) := by
  let a := fraction A B
  let c := fraction C D
  let x := sample p A B
  let y := sample q C D
  let U := unit p
  let V := unit q
  let W := B*(U*V)
  have hu := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive q)
  have hw := positive_product _ _ hA.andE₂ hu
  have e : Γ ⊢[PRAAx] a ≐ c :=
    GaussianStirlingOddCoefficients.fraction_equal A B C D hA.andE₂ hC.andE₂
      (h.eqTrans (mul_comm B C))
  have log : Γ ⊢[PRAAx] distanceBounded x y (U+V) (U*V) :=
    cross_at logF logF (data A B) (data C D) p q
      (GaussianPositiveRationalLogarithmProperness.original_logarithm_proper A B C D hA hC h)
  have product : Γ ⊢[PRAAx] distanceBounded (qmul a x) (qmul a y) (A*(U+V)) W :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference a x y).eqSymm
      (.eqRefl _) (.eqRefl _)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hA.andE₂ hu (fraction_bound A B hA.andE₂) log)
  have shifted := GaussianNamedDifference.difference_distance (qmul a x) (qmul a y) a a (A*(U+V)) zero W hw
    product (GaussianRationalPowerDifference.distance_refl_zero a W hw)
  exact distance_congr (.eqRefl _) (qsub_congr (qmul_congr e (.eqRefl y)) e)
    (add_zero _) (.eqRefl _) shifted

theorem scaled_to_original (p N A D : PTm n)
    (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] source A D) :
    Γ ⊢[PRAAx] distanceBounded (primitive p (A*N) (D*N)) (primitive p A D) (two*A) (D*unit p) := by
  let U := unit p
  have hu := unit_positive (Γ := Γ) p
  have ha := positive_product A N h.andE₁ hN
  have hd := positive_product D N h.andE₂ hN
  have raw := equal_ratio p p (A*N) (D*N) A D (.andI ha hd) h (by ipra_ring)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hd (positive_product _ _ hu hu))
    (positive_product _ _ h.andE₂ hu) (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem actual_positive_logarithm_primitive_rescale_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ source (var 2) (var 3)) ⟶
        distanceBounded (primitive (var 0) (var 2*var 1) (var 3*var 1)) (primitive (var 0) (var 2) (var 3))
          (two*var 2) (var 3*unit (var 0))) :=
  closeUniv 4 (.impI (scaled_to_original _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeLogPrimitiveRescale
