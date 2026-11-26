import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneRadialLogarithm
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRightHalfPlaneArgumentProperness
import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRightHalfPlaneArgumentAxis
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary

/-!
# Canonical logarithm on the encoded rational right half-plane

The input has real numerator A > 0, imaginary magnitude B, common
denominator D > 0, and imaginary sign bit. The program adds the original
half-logarithm of the squared modulus to the signed imaginary arctangent.
Positive rational scaling adds the original real logarithm, and on the
positive real axis this program agrees with that logarithm.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open GaussianNameRingLaws (zeroF zero_fast add_associative)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalHorner (positive_product)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "G" => GaussianRightHalfPlaneArgument.nameF
local notation "X" => GaussianRightHalfPlaneRadialLogarithm.data
local notation "Y" => GaussianRightHalfPlaneArgument.data
local notation "L" => GaussianPositiveRationalLogarithm.data

def source (A D neg : PTm n) : Fm PTm n := GaussianRightHalfPlaneArgument.source A neg ⋏ le one D
def nameF : PR 2 := addF F G
def data (A B D neg : PTm n) : PTm n := addData (X A B D) (Y A B neg)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (data A B D neg) = data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [data]

theorem regular (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] pointCN nameF (data A B D neg) :=
  add_fast F G _ _
    (GaussianRightHalfPlaneRadialLogarithm.regular A B D h.andE₁.andE₁ h.andE₂)
    (GaussianRightHalfPlaneArgument.name_regular A B neg h.andE₁)

theorem positive_axis (A D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] crossEquivalent nameF logF (data A zero D neg) (L A D) := by
  let x := X A zero D
  let y := Y A zero neg
  let a := L A D
  let z := GaussianRightHalfPlaneArgument.unsignedData A zero
  have ha := GaussianPositiveRationalLogarithm.name_regular A D (.andI h.andE₁.andE₁ h.andE₂)
  have hx := GaussianRightHalfPlaneRadialLogarithm.regular A zero D h.andE₁.andE₁ h.andE₂
  have hy := GaussianRightHalfPlaneArgument.name_regular A zero neg h.andE₁
  have realEq := GaussianRightHalfPlaneRadialLogarithm.positive_axis A D h.andE₁.andE₁ h.andE₂
  have imagEq := GaussianRightHalfPlaneArgumentAxis.zero_axis_cross A neg h.andE₁
  have imagZero := cross_trans _ _ _ _ _ _ imagEq (GaussianGammaRationalWendelBoundary.zero_data_cross z a)
  exact cross_trans _ _ _ _ _ _
    (add_cross F logF G zeroF x a y a hx ha hy (zero_fast a) realEq imagZero) (GaussianNameRingLaws.add_zero logF a ha)

theorem positive_scaling (A B D neg c d : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hc : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source c d) :
    Γ ⊢[PRAAx] crossEquivalent nameF (addF logF nameF) (data (c*A) (c*B) (d*D) neg)
      (addData (L c d) (data A B D neg)) := by
  let x := X A B D
  let y := Y A B neg
  let u := X (c*A) (c*B) (d*D)
  let v := Y (c*A) (c*B) neg
  let l := L c d
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have hA' := positive_product c A hc.andE₁ hA
  have hD' := positive_product d D hc.andE₂ hD
  have hx := GaussianRightHalfPlaneRadialLogarithm.regular A B D hA hD
  have hu := GaussianRightHalfPlaneRadialLogarithm.regular (c*A) (c*B) (d*D) hA' hD'
  have hy := GaussianRightHalfPlaneArgument.name_regular A B neg h.andE₁
  have hs : Γ ⊢[PRAAx] GaussianRightHalfPlaneArgument.source (c*A) neg := .andI hA' h.andE₁.andE₂
  have hv := GaussianRightHalfPlaneArgument.name_regular (c*A) (c*B) neg hs
  have hl := GaussianPositiveRationalLogarithm.name_regular c d hc
  have realEq := GaussianRightHalfPlaneRadialLogarithm.positive_scaling A B D c d hA hD hc
  have imagEq := GaussianRightHalfPlaneArgumentProperness.equal_ratio (c*A) (c*B) A B neg hs hA (by ipra_ring)
  have parts := add_cross F (addF logF F) G G u (addData l x) v y
    hu (add_fast logF F l x hl hx) hv hy realEq imagEq
  exact cross_trans _ _ _ _ _ _ parts (add_associative logF F G l x y hl hx hy)

theorem actual_right_half_plane_logarithm_regular_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 2) (var 3) ⟶ pointCN nameF (data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (regular _ _ _ _ Prf.hyp0))

theorem actual_right_half_plane_logarithm_positive_axis_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (source (var 0) (var 1) (var 2) ⟶ crossEquivalent nameF logF
        (data (var 0) zero (var 1) (var 2)) (L (var 0) (var 1))) :=
  closeUniv 3 (.impI (positive_axis _ _ _ Prf.hyp0))

theorem actual_right_half_plane_logarithm_positive_scaling_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 2) (var 3) ⟶ GaussianPositiveRationalLogarithm.source (var 4) (var 5) ⟶
        crossEquivalent nameF (addF logF nameF) (data (var 4*var 0) (var 4*var 1) (var 5*var 2) (var 3))
          (addData (L (var 4) (var 5)) (data (var 0) (var 1) (var 2) (var 3)))) :=
  closeUniv 6 (.impI (.impI (positive_scaling _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithm
