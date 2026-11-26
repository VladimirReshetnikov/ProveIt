import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.GaussianBinetReciprocalRows
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmIncrement
import IPRADerivations.Analysis.Logarithm.RightHalfPlane.GaussianRightHalfPlaneLogarithmIncrementMargin

/-!
# Actual logarithm sample increments on a horizontal mesh

The canonical logarithm has the checked local quadratic estimate.
For a positive horizontal displacement its linear term is exactly the
actual reciprocal of the left endpoint times the literal mesh width.
The bound here compares the original logarithm observations directly.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLogHorizontalStep

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq normSq_one normSq_scale oneCode scale)
open GaussianBinetReciprocalRows (same_imaginary_shift)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qmul represents_congr)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical qsub_represents)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source nameF data)
open GaussianRightHalfPlaneLogarithmIncrementMargin (admitted smallStep)
open GaussianRightHalfPlaneLogarithmRelativeStep (relative relative_binding)
open GaussianRootAlgebra (equal_symm normSq_equal sub)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step (H D : PTm n) : PTm n := ofGaussian (scale H oneCode) D

ipra_subst step

theorem relative_horizontal (A B D neg H : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    relative (native A B neg) (native (A+H) B neg) ≐ qmul (step H D) (reciprocal (argument A B D neg)) := by
  let u := native A B neg
  let v := native (A+H) B neg
  have hA := h.andE₁.andE₁
  have hd := h.andE₂
  have hu : Γ ⊢[PRAAx] le one (normSq u) :=
    le_trans (positive_product A A hA hA)
      (le_congr (.eqRefl _) (native_norm A B neg h.andE₁.andE₂).eqSymm (le_add_right (A*A) (B*B)))
  let w := qsub (ofGaussian v D) (ofGaussian u D)
  have rep := qsub_represents (ofGaussian v D) (ofGaussian u D) v u D hd
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  have disp : Γ ⊢[PRAAx] w ≐ step H D :=
    canonical_unique _ _ (scale H oneCode) D (qsub_canonical _ _) (ofGaussian_canonical _ _ hd) hd
      (represents_congr (.eqRefl _) (same_imaginary_shift A H B neg) (.eqRefl _) rep)
      (ofGaussian_represents _ _ hd)
  exact (relative_binding u v D hd hu).eqSymm.eqTrans (qmul_congr disp (.eqRefl _))

theorem native_step_bounded (A B neg H : PTm n) : Γ ⊢[PRAAx]
    ComplexLogarithmRemainder.bounded (sub (native (A+H) B neg) (native A B neg)) H := by
  have e : Γ ⊢[PRAAx] normSq (sub (native (A+H) B neg) (native A B neg)) ≐ H*H :=
    (normSq_equal (same_imaginary_shift A H B neg)).eqTrans
      ((normSq_scale H oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)))
  exact le_congr e.eqSymm (.eqRefl _) (le_refl _)

theorem sample_error (p A B D neg H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*A))
    (hsize : Γ ⊢[PRAAx] le (A+B+(A+H)+B) (C*D)) (hsmall : Γ ⊢[PRAAx] smallStep H K C D) : Γ ⊢[PRAAx]
    distanceBounded (qsub (ap2 nameF p (data (A+H) B D neg)) (ap2 nameF p (data A B D neg)))
      (qmul (step H D) (reciprocal (argument A B D neg)))
      (num 4*H*H*unit p+num 9*(A*A)) (A*A*unit p) := by
  let x := data (A+H) B D neg
  let y := data A B D neg
  let U := unit p
  let V := A*A*U
  let raw := qsub (ap2 nameF p x) (ap2 nameF p y)
  let mid := ap2 (GaussianNamedDifference.nameF nameF nameF) p (GaussianNamedDifference.data x y)
  let lin := relative (native A B neg) (native (A+H) B neg)
  have hA := h.andE₁.andE₁
  have hu := unit_positive (Γ := Γ) p
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ hA hA) hu
  have g : Γ ⊢[PRAAx] source (A+H) D neg := .andI (.andI (le_trans hA (le_add_right A H)) h.andE₁.andE₂) h.andE₂
  have hnext := le_trans hmargin (le_mul_mono (le_refl K) (le_add_right A H))
  have hi := admitted A B neg (A+H) B neg D H K C h g (native_step_bounded A B neg H) hK hmargin hnext hsize hsmall
  have localStep : Γ ⊢[PRAAx] distanceBounded mid lin (num 4*H*H*U+num 3*(A*A)) V :=
    GaussianRightHalfPlaneLogarithmIncrement.sample_error p A B neg (A+H) B neg D H _ _ hi
  have compare : Γ ⊢[PRAAx] distanceBounded mid raw (num 6) U := GaussianNamedDifference.sample_error nameF nameF x y p
    (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ g) (GaussianRightHalfPlaneLogarithm.regular _ _ _ _ h)
  have first := distance_radius_mono raw mid (num 6) U (num 6*(A*A)) V hu hv
    (by dsimp only [V, U]; ipra_le 0) (distance_symmetric mid raw (num 6) U hu compare)
  exact distance_congr (.eqRefl _) (relative_horizontal A B D neg H h) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same raw mid lin (num 6*(A*A)) (num 4*H*H*U+num 3*(A*A)) V hv first localStep)

theorem actual_horizontal_logarithm_sample_linear_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 3) (var 4) ⟶
      (le one (var 6) ⋏ le (var 3) (var 6*var 1)) ⟶
      (le (var 1+var 2+(var 1+var 5)+var 2) (var 7*var 3) ⋏ smallStep (var 5) (var 6) (var 7) (var 3)) ⟶
        distanceBounded (qsub (ap2 nameF (var 0) (data (var 1+var 5) (var 2) (var 3) (var 4)))
          (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4))))
          (qmul (step (var 5) (var 3)) (reciprocal (argument (var 1) (var 2) (var 3) (var 4))))
          (num 4*var 5*var 5*unit (var 0)+num 9*(var 1*var 1)) (var 1*var 1*unit (var 0))) :=
  closeUniv 8 (.impI (.impI (.impI (sample_error _ _ _ _ _ _ _ _ hyp2 Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianBinetLogHorizontalStep
