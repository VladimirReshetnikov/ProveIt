import IPRADerivations.Analysis.Trigonometry.Cyclic.Chords.GaussianCyclicRootHalfAngle
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianCoordinateRadius

/-!
# Sampled lower margin for a positive half-angle sine

The actual sine sample inherits a fractional modulus lower bound from
the original division-angle chord. The external inequality is converted
to a cleared signed numerator judgment before the square comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianCyclicHalfSineMargin

open_ipra
open GaussianArctangentDivisionAngles (coefficient source)
open GaussianArctangentDivisionSinePositive (sine_lower exactSineData)
open GaussianNamedSineFromExponential (sineF)
open GaussianNamedPositiveExponentialOrder (real_order_at)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_congr upper_mono positive_cancel)
open RationalRepresentedUpper (left right to_signed)
open GaussianRationalHorner (ofGaussian_represents scalar_congr positive_product)
open GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open GaussianRationalLowerBounds (lower lower_from_representation)
open ComplexLogarithmRemainder (re normSq)
open GaussianRelativeNormTriangle (signed_le_absolute)
open LeanProofs.IPRA.Foundations.GapDecision (zabs)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "D" => GaussianArctangentDivisionAngles.nameF

def sineSample (p d m x : PTm n) : PTm n := ap2 (sineF D) p (exactSineData d m x)

ipra_subst sineSample [exactSineData, two, one]

private theorem chord_at (p d m x : PTm n) (h : Γ ⊢[PRAAx] source d m) :
    Γ ⊢[PRAAx] upper (fstT (coefficient d m)) (fstT (sineSample p d m x)) two (unit p) := by
  let U := unit p
  let a := coefficient d m
  let d' := exactSineData d m x
  have hp := unit_positive (Γ := Γ) p
  have raw := upper_congr (congrFst (constant_at p a)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (real_order_at constantF (sineF D) a d' p p (sine_lower d m x h))
  exact RationalValueBounds.upper_two_errors_same hp raw

theorem sine_lower_at (p d m x : PTm n) (h : Γ ⊢[PRAAx] source d m)
    (hd : Γ ⊢[PRAAx] le one d) (hp : Γ ⊢[PRAAx] le (two*m) (unit p)) :
    Γ ⊢[PRAAx] lower (sineSample p d m x) d m := by
  let q := sineSample p d m x
  let U := unit p
  let a := rawGaussian q
  let E := rawDen q
  let r := re a
  let t := coefficient d m
  let L := left (ZT.ofNat (two*d)) E U
  let H := right r m E two U
  let W := ZT.ofNat (zabs r)
  have he := raw_den_positive (Γ := Γ) q
  have tp : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT t) (ZT.ofNat (two*d)) m := by
    apply scalar_congr (.eqRefl _) ?_ (.eqRefl _) (ofGaussian_represents _ _ h.andE₁).andE₁
    apply ZT.derive
    simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.re_one, ZT.toZ_ofNat,mul_one]
  have signed : Γ ⊢[PRAAx] zle L H :=
    to_signed _ _ _ _ m E two U tp (raw_represents q).andE₁ (chord_at p d m x h)
  have room : Γ ⊢[PRAAx] le ((two*m)*E) (d*U*E) :=
    le_mul_mono (le_trans hp (le_congr (one_mul U) (.eqRefl _) (le_mul_mono hd (le_refl U)))) (le_refl E)
  have realLower : Γ ⊢[PRAAx] le (d*E) (m*zabs r) := by
    apply positive_cancel (unit_positive p)
    let δ₁ := monus (H.pos+L.neg) (L.pos+H.neg)
    let δ₂ := monus (W.pos+r.neg) (r.pos+W.neg)
    let δ₃ := monus (d*U*E) ((two*m)*E)
    refine le_of_eq_add (d := δ₁+(m*U)*δ₂+δ₃) ?_
    have s1 := zle_toZ signed
    have s2 : ZT.toZ Γ r+𝔞 δ₂ = ZT.toZ Γ W := zle_toZ (signed_le_absolute r)
    have s3 := natEq (eq_add_of_le room)
    apply deriveNat
    dsimp only [L,H,W,δ₁,δ₂,δ₃] at s1 s2 ⊢
    simp only [left,right,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat] at s1 s2 ⊢
    ipra_simps
    linear_combination -s1-𝔞 m*𝔞 U*s2+s3
  have component : Γ ⊢[PRAAx] le (zabs r*zabs r) (normSq a) :=
    le_congr (.eqRefl _) (GaussianCoordinateRadius.native_squared a).eqSymm (le_add_right _ _)
  have squared := le_mul_mono realLower realLower
  exact lower_from_representation _ _ _ _ _ he h.andE₁ (raw_represents q)
    (le_trans (le_congr (by ipra_ring) (by ipra_ring) squared)
      (le_mul_mono (le_refl (m*m)) component))

theorem actual_positive_half_sine_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 2) (var 1) ⋏ le one (var 2)) ⟶ le (two*var 1) (unit (var 3)) ⟶
      lower (sineSample (var 3) (var 2) (var 1) (var 0)) (var 2) (var 1)) :=
  closeUniv 4 (.impI (.impI (sine_lower_at _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianCyclicHalfSineMargin
