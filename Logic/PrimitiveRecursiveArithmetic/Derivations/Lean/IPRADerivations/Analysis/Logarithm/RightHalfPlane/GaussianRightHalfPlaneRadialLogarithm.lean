import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalHalfLogarithm
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositiveTimePowerProduct
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingDuplicationConstant

/-!
# Real part of the right-half-plane logarithm

Use the squared radius from the signed numerator and common denominator.
The evaluator has the original positive rational logarithm as its real-axis
restriction, and positive rational scaling adds the original real logarithm.
Both imaginary signs have the same radial evaluator.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneRadialLogarithm

open_ipra
open ComplexLogarithmRemainder (code normSq normSq_code)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product)
open RationalGaussianEmbedding (embed embed_canonical embed_from_representation)
open GaussianRationalMetric (qnormSq qnormSq_represents)
open GaussianNamedBoundedSquareRoot (sqrtF)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianPositiveRationalHalfLogarithm.nameF
local notation "R" => GaussianPositiveRationalHalfLogarithm.data
local notation "L" => GaussianPositiveRationalLogarithm.data
local notation "E" => GaussianRadiusExponentialName.nameF

def normNum (A B : PTm n) : PTm n := A*A+B*B
def normDen (D : PTm n) : PTm n := D*D
abbrev nameF : PR 2 := H
def data (A B D : PTm n) : PTm n := R (normNum A B) (normDen D)
def exponentialData (A B D : PTm n) : PTm n :=
  GaussianPositiveRationalHalfLogarithm.exponentialData (normNum A B) (normDen D)

ipra_subst data [normNum, normDen]

theorem log_source (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (normNum A B) (normDen D) :=
  .andI (le_trans (positive_product A A hA hA) (le_add_right _ _)) (positive_product D D hD hD)

theorem regular (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D) :=
  GaussianPositiveRationalHalfLogarithm.regular _ _ (log_source A B D hA hD)

theorem modulus_square (A B D : PTm n) (i : ZT n) (hD : Γ ⊢[PRAAx] le one D)
    (hi : Γ ⊢[PRAAx] ZT.eq i (ZT.ofNat B) ⋎ ZT.eq i (-(ZT.ofNat B))) :
    Γ ⊢[PRAAx] embed (qnormSq (ofGaussian (code (ZT.ofNat A) i) D)) ≐ fraction (normNum A B) (normDen D) := by
  let z := code (ZT.ofNat A) i
  let q := ofGaussian z D
  let a := normNum A B
  let b := normDen D
  let f := fraction a b
  have en : Γ ⊢[PRAAx] normSq z ≐ a := by
    refine .orE hi ?_ ?_
    · have eq := ZT.toZ_eq (Prf.hyp0 : ZT.eq i (ZT.ofNat B) :: Γ ⊢[PRAAx] ZT.eq i (ZT.ofNat B))
      apply deriveNat
      rw [show z = code (ZT.ofNat A) i from rfl, normSq_code, eq]
      simp only [a,normNum,ZT.toZ_ofNat]
      ipra_simps
      ring
    · have eq := ZT.toZ_eq (Prf.hyp0 : ZT.eq i (-(ZT.ofNat B)) :: Γ ⊢[PRAAx] ZT.eq i (-(ZT.ofNat B)))
      apply deriveNat
      rw [show z = code (ZT.ofNat A) i from rfl, normSq_code, eq]
      simp only [a,normNum,ZT.toZ_neg,ZT.toZ_ofNat]
      ipra_simps
      ring
  have hb := positive_product D D hD hD
  have rep := qnormSq_represents q z D hD (ofGaussian_represents z D hD)
  have eqZ : Γ ⊢[PRAAx] ZT.eq (ZT.ofNat (normSq z)) (ZT.ofNat a) := by
    apply ZT.derive
    simp only [ZT.toZ_ofNat,natEq en]
  have scalar := GaussianRationalHorner.scalar_congr (.eqRefl _) eqZ (.eqRefl _) rep
  have left := embed_from_representation (qnormSq q) (ZT.ofNat a) b scalar
  have right := ofGaussian_represents (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) b hb
  have changeNum : Γ ⊢[PRAAx] GaussianRootAlgebra.equal (RationalGaussianEmbedding.native (ZT.ofNat a))
      (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring
  exact GaussianRationalHorner.canonical_unique _ f _ b (embed_canonical _)
    (GaussianRationalHorner.ofGaussian_canonical _ _ hb) hb
    (GaussianRationalHorner.represents_congr (.eqRefl _) changeNum (.eqRefl _) left) right

theorem exponential_square_root (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent (E nameF) (sqrtF constantF)
      (exponentialData A B D) (fraction (normNum A B) (normDen D)) :=
  GaussianPositiveRationalHalfLogarithm.exponential_square_root _ _ (log_source A B D hA hD)

theorem half_square_logarithm (a b : PTm n) (h : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source a b) :
    Γ ⊢[PRAAx] crossEquivalent H logF (R (a*a) (b*b)) (L a b) := by
  let x := L a b
  let y := L (a*a) (b*b)
  have hx := GaussianPositiveRationalLogarithm.name_regular a b h
  have hsq := log_source a zero b h.andE₁ h.andE₂
  have hy := GaussianPositiveRationalLogarithm.name_regular (a*a) (b*b)
    (.andI (positive_product a a h.andE₁ h.andE₁) hsq.andE₂)
  have eq := GaussianEulerPositiveTimePowerProduct.logarithm_product a b a b (.andI h h)
  exact cross_trans _ _ _ _ _ _
    (GaussianNamedHalf.proper logF (addF logF logF) y (addData x x) hy (add_fast _ _ _ _ hx hx) eq)
    (GaussianStirlingDuplicationConstant.scale_half_double logF x hx)

theorem positive_axis (A D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent nameF logF (data A zero D) (L A D) := by
  have h := log_source A zero D hA hD
  have hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (A*A) (D*D) :=
    .andI (positive_product A A hA hA) h.andE₂
  have eq := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper
    (normNum A zero) (D*D) (A*A) (D*D) h hs (by unfold normNum; ipra_ring)
  exact cross_trans _ _ _ _ _ _ (GaussianNamedHalf.proper _ _ _ _
    (GaussianPositiveRationalLogarithm.name_regular _ _ h) (GaussianPositiveRationalLogarithm.name_regular _ _ hs) eq)
    (half_square_logarithm A D (.andI hA hD))

theorem positive_scaling (A B D c d : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hD : Γ ⊢[PRAAx] le one D) (hc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source c d) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF logF nameF) (data (c*A) (c*B) (d*D))
      (addData (L c d) (data A B D)) := by
  let a := normNum A B
  let b := normDen D
  let u := normNum (c*A) (c*B)
  let v := normDen (d*D)
  let x := L (c*c) (d*d)
  let y := L a b
  let z := L (c*c*a) (d*d*b)
  have h := log_source A B D hA hD
  have h' := log_source (c*A) (c*B) (d*D) (positive_product c A hc.andE₁ hA)
    (positive_product d D hc.andE₂ hD)
  have hs : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (c*c) (d*d) :=
    .andI (positive_product c c hc.andE₁ hc.andE₁) (positive_product d d hc.andE₂ hc.andE₂)
  have hz : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source (c*c*a) (d*d*b) :=
    .andI (positive_product _ _ hs.andE₁ h.andE₁) (positive_product _ _ hs.andE₂ h.andE₂)
  have hx := GaussianPositiveRationalLogarithm.name_regular _ _ hs
  have hy := GaussianPositiveRationalLogarithm.name_regular _ _ h
  have e := GaussianPositiveRationalLogarithmProperness.original_logarithm_proper u v (c*c*a) (d*d*b) h' hz
    (by dsimp [u,v,a,b,normNum,normDen]; ipra_ring)
  have product := GaussianEulerPositiveTimePowerProduct.logarithm_product (c*c) (d*d) a b (.andI hs h)
  have moved := GaussianNamedHalf.proper logF (addF logF logF) (L u v) (addData x y)
    (GaussianPositiveRationalLogarithm.name_regular _ _ h') (add_fast _ _ _ _ hx hy)
    (cross_trans _ _ _ _ _ _ e product)
  have dist := GaussianNameRingLaws.distributive constantF logF logF
    (GaussianEulerSquareFactorInverse.half : PTm n) x y (constant_regular _) hx hy
  have add := add_cross H logF H H (GaussianNamedHalf.data logF x) (L c d)
    (GaussianNamedHalf.data logF y) (GaussianNamedHalf.data logF y)
    (GaussianNamedHalf.regular _ _ hx) (GaussianPositiveRationalLogarithm.name_regular c d hc)
    (GaussianNamedHalf.regular _ _ hy) (GaussianNamedHalf.regular _ _ hy)
    (half_square_logarithm c d hc) (cross_refl _ _ (GaussianNamedHalf.regular _ _ hy))
  exact cross_trans _ _ _ _ _ _ moved (cross_trans _ _ _ _ _ _ dist add)

theorem actual_right_half_plane_radial_exponential_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ le one (var 2)) ⟶ crossEquivalent (E nameF) (sqrtF constantF)
        (exponentialData (var 0) (var 1) (var 2)) (fraction (normNum (var 0) (var 1)) (normDen (var 2)))) :=
  closeUniv 3 (.impI (exponential_square_root _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_right_half_plane_radial_positive_axis_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le one (var 0) ⋏ le one (var 1)) ⟶ crossEquivalent nameF logF (data (var 0) zero (var 1)) (L (var 0) (var 1))) :=
  closeUniv 2 (.impI (positive_axis _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_right_half_plane_radial_scaling_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((le one (var 0) ⋏ (le one (var 2) ⋏ GaussianPositiveRationalLogarithm.source (var 3) (var 4))) ⟶
        crossEquivalent nameF (addF logF nameF) (data (var 3*var 0) (var 3*var 1) (var 4*var 2))
          (addData (L (var 3) (var 4)) (data (var 0) (var 1) (var 2)))) :=
  closeUniv 5 (.impI (positive_scaling _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneRadialLogarithm
