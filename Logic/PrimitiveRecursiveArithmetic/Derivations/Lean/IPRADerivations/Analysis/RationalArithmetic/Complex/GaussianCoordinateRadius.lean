import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality
import IPRADerivations.Analysis.RationalArithmetic.RationalValueBounds
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalDirectionNormalizer

/-!
# Coordinate bounds from the original Gaussian distance

The two separately stored rational coordinates inherit the same radius
from a Euclidean distance bound. The proof uses the actual common integer
numerators and cancels their positive common denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCoordinateRadius

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_sq)
open GaussianL1 (abs_multiply abs_ofNat)
open GaussianRationalHorner (represents)
open GaussianRationalMetric (distanceBounded bounded_difference_iff)
open GaussianRationalValueEquality
  (commonDen leftValue rightValue common_den_positive common_left_represents common_right_represents)
open GaussianRootAlgebra (sub re_sub im_sub)
open ComplexLogarithmRemainder (re im normSq normSq_eval)
open RationalSupMetric (numeratorOf denominatorOf)
open RationalValueBounds (cross radius positive_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem scaled_cross (a b E : PTm n) (u v : ZT n)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents a u E)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b v E) :
    Γ ⊢[PRAAx] E*zabs (cross a b) ≐ (denominatorOf a*denominatorOf b)*zabs (u-v) := by
  have e : ZT.toZ Γ (ZT.ofNat E*cross a b) =
      ZT.toZ Γ (ZT.ofNat (denominatorOf a*denominatorOf b)*(u-v)) := by
    have ea := ZT.toZ_eq ha
    have eb := ZT.toZ_eq hb
    simp only [ZT.toZ_mul, ZT.toZ_ofNat] at ea eb
    simp only [cross, ZT.toZ_mul, ZT.toZ_sub, ZT.toZ_ofNat]
    ipra_simps
    linear_combination -𝔞(denominatorOf b)*ea+𝔞(denominatorOf a)*eb
  have product (D : PTm n) (w : ZT n) : Γ ⊢[PRAAx] zabs (ZT.ofNat D*w) ≐ D*zabs w :=
    (abs_multiply _ _).eqTrans (congrMul (abs_ofNat D) (.eqRefl _))
  exact (product _ _).eqSymm.eqTrans ((zabs_congr e).eqTrans (product _ _))

theorem scalar_bound (a b E A B : PTm n) (u v : ZT n)
    (hE : Γ ⊢[PRAAx] le one E)
    (ha : Γ ⊢[PRAAx] RationalArithmetic.represents a u E)
    (hb : Γ ⊢[PRAAx] RationalArithmetic.represents b v E)
    (h : Γ ⊢[PRAAx] le (B*zabs (u-v)) (A*E)) :
    Γ ⊢[PRAAx] radius a b A B := by
  apply positive_cancel hE
  have left : Γ ⊢[PRAAx] E*(B*zabs (cross a b)) ≐
      (B*zabs (u-v))*(denominatorOf a*denominatorOf b) := by
    ipra_lc 𝔞(B)*natEq (scaled_cross a b E u v ha hb)
  exact le_congr left.eqSymm (by ipra_ring)
    (mul_le_mul_right (denominatorOf a*denominatorOf b) h)

theorem native_squared (z : PTm n) : Γ ⊢[PRAAx] normSq z ≐
    zabs (re z)*zabs (re z)+zabs (im z)*zabs (im z) := by
  apply deriveNat
  rw [normSq_eval]
  simp only [Q.mk_add, map_add]
  rw [zabs_sq,zabs_sq]
  ring

theorem native_coordinates (z A B E : PTm n)
    (h : Γ ⊢[PRAAx] le ((B*B)*normSq z) ((A*A)*(E*E))) :
    Γ ⊢[PRAAx] le (B*zabs (re z)) (A*E) ⋏ le (B*zabs (im z)) (A*E) := by
  have shape := native_squared (Γ := Γ) z
  have hr := le_congr (.eqRefl _) shape.eqSymm (le_add_right (zabs (re z)*zabs (re z)) (zabs (im z)*zabs (im z)))
  have hi := le_congr (.eqRefl _) shape.eqSymm (le_add_left (zabs (im z)*zabs (im z)) (zabs (re z)*zabs (re z)))
  have h' := le_congr (mul_comm _ _) (.eqRefl _) h
  exact .andI
    (nat_sqrt_mono (le_congr (by ipra_ring) (by ipra_ring) (le_trans (mul_le_mul_right (B*B) hr) h')))
    (nat_sqrt_mono (le_congr (by ipra_ring) (by ipra_ring) (le_trans (mul_le_mul_right (B*B) hi) h')))

theorem coordinates_of_representations (q r a b E A B : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hq : Γ ⊢[PRAAx] represents q a E) (hr : Γ ⊢[PRAAx] represents r b E)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    radius (fstT q) (fstT r) A B ⋏ radius (sndT q) (sndT r) A B := by
  have cleared := (bounded_difference_iff q r a b E A B hE hB hq hr).iffMp h
  have both := native_coordinates (sub a b) A B E cleared
  have real : Γ ⊢[PRAAx] zabs (re (sub a b)) ≐ zabs (re a-re b) :=
    zabs_congr (by rw [ZT.toZ_sub, re_sub])
  have imaginary : Γ ⊢[PRAAx] zabs (im (sub a b)) ≐ zabs (im a-im b) :=
    zabs_congr (by rw [ZT.toZ_sub, im_sub])
  exact .andI
    (scalar_bound _ _ _ _ _ _ _ hE (.andE₁ hq) (.andE₁ hr)
      (le_congr (congrMul (.eqRefl _) real) (.eqRefl _) (.andE₁ both)))
    (scalar_bound _ _ _ _ _ _ _ hE (.andE₂ hq) (.andE₂ hr)
      (le_congr (congrMul (.eqRefl _) imaginary) (.eqRefl _) (.andE₂ both)))

theorem coordinates (q r A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] distanceBounded q r A B) : Γ ⊢[PRAAx]
    radius (fstT q) (fstT r) A B ⋏ radius (sndT q) (sndT r) A B :=
  coordinates_of_representations q r (leftValue q r) (rightValue q r) (commonDen q r) A B
    (common_den_positive q r) hB (common_left_represents q r) (common_right_represents q r) h

theorem original_gaussian_coordinate_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (var 0) (var 1) (var 2) (var 3) ⟶
      (radius (fstT (var 0)) (fstT (var 1)) (var 2) (var 3) ⋏
        radius (sndT (var 0)) (sndT (var 1)) (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (coordinates _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCoordinateRadius
