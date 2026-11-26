import IPRADerivations.Analysis.Barnes.Logarithms.GaussianBarnesVignerasLogQuotient
import IPRADerivations.Core.LinearCombination

/-!
# Rational chart independence of the actual Barnes logarithmic quotient

Rational mesh denominators and certified candidate logarithm radii can
be changed independently. The original candidate values at the two
presentations supply the only candidate compatibility hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasQuotientProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code scale)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianNamedDifferenceQuotientProperness (difference_proper)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  positive_product represents_congr represents_rescale)
open GaussianRealNameExponentialInjectivity (independent_radii_injective)
open GaussianRootAlgebra (equal equal_of_values equal_symm re_scale im_scale)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Log" => GaussianNamedPositiveLogarithm.nameF
local notation "logd" => GaussianNamedPositiveLogarithm.data
local notation "L" => GaussianBarnesCanonicalPositiveLogarithm.nameF
local notation "ld" => GaussianBarnesCanonicalPositiveLogarithm.data
local notation "Q" => GaussianBarnesVignerasLogQuotient.nameF
local notation "qd" => GaussianBarnesVignerasLogQuotient.data

theorem centers_equal (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d)
    (e : Γ ⊢[PRAAx] a*d ≐ c*b) : Γ ⊢[PRAAx] ofGaussian (center a b) b ≐ ofGaussian (center c d) d := by
  let x := ofGaussian (center a b) b
  let y := ofGaussian (center c d) d
  have u := represents_rescale x (center a b) b d (ofGaussian_represents _ _ hb)
  have v := represents_rescale y (center c d) d b (ofGaussian_represents _ _ hd)
  have eq : Γ ⊢[PRAAx] equal (scale d (center a b)) (scale b (center c d)) := by
    apply equal_of_values
    · ipra_lc [re_scale,center,eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat] natEq e
    · simp only [im_scale,center,eval_im_code,ZT.toZ_ofNat]
      (try ipra_simps) <;> ring
  exact canonical_unique x y (scale d (center a b)) (b*d) (ofGaussian_canonical _ _ hb) (ofGaussian_canonical _ _ hd)
    (positive_product _ _ hb hd) u (represents_congr (.eqRefl _) (equal_symm eq) (mul_comm _ _) v)

theorem candidate_log_proper (f : PR 2) (x y P T M N : PTm n)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T)
    (hy : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f y M N)
    (he : Γ ⊢[PRAAx] crossEquivalent f f x y) :
    Γ ⊢[PRAAx] crossEquivalent (Log f) (Log f) (logd x P) (logd y M) := by
  have fx := GaussianNamedPositiveLogarithmExponential.original_recovery f x P T hx
  have fy := GaussianNamedPositiveLogarithmExponential.original_recovery f y M N hy
  exact independent_radii_injective (Log f) (Log f) (GaussianCompactLogarithmBounds.radius P T)
    (GaussianCompactLogarithmBounds.radius M N) _ _
    (GaussianNamedPositiveLogarithm.exponential_input f x P T hx) (GaussianNamedPositiveLogarithm.exponential_input f y M N hy)
    (GaussianNamedPositiveLogarithm.real_samples f x P) (GaussianNamedPositiveLogarithm.real_samples f y M)
    (cross_trans _ _ _ _ _ _ fx (cross_trans _ _ _ _ _ _ he (cross_symm _ _ _ _ fy)))

theorem proper (f : PR 2) (a b c d x y P T M N : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (hx : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f x P T)
    (hy : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source f y M N)
    (hp : Γ ⊢[PRAAx] a*d ≐ c*b) (he : Γ ⊢[PRAAx] crossEquivalent f f x y) :
    Γ ⊢[PRAAx] crossEquivalent (Q f) (Q f) (qd a b x P) (qd c d y M) := by
  have hA := GaussianBarnesCanonicalPositiveLogarithm.default_source a b ha hb
  have hC := GaussianBarnesCanonicalPositiveLogarithm.default_source c d hc hd
  exact difference_proper (Log f) (Log f) L L (logd x P) (logd y M) (ld a b (a+b)) (ld c d (c+d))
    (GaussianNamedPositiveLogarithm.name_regular f x P T hx) (GaussianNamedPositiveLogarithm.name_regular f y M N hy)
    (GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ hA) (GaussianBarnesCanonicalPositiveLogarithm.regular _ _ _ hC)
    (candidate_log_proper f x y P T M N hx hy he)
    (GaussianBarnesCanonicalPositiveLogarithmRealAxis.proper a b c d (a+b) (c+d) hA hC (centers_equal a b c d hb hd hp))

theorem actual_Barnes_candidate_log_quotient_chart_proper_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (let a := var 0
     let b := var 1
     let c := var 2
     let d := var 3
     let x := var 4
     let y := var 5
     let P := var 6
     let T := var 7
     let M := var 8
     let N := var 9
     ((le one a ⋏ le one b) ⋏ (le one c ⋏ le one d)) ⟶
     ((GaussianNamedPositiveLogarithm.source f x P T ⋏ GaussianNamedPositiveLogarithm.source f y M N) ⋏
       ((a*d ≐ c*b) ⋏ crossEquivalent f f x y)) ⟶
       crossEquivalent (Q f) (Q f) (qd a b x P) (qd c d y M)) :=
  closeUniv 10 (.impI (.impI (proper f _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasQuotientProperness
