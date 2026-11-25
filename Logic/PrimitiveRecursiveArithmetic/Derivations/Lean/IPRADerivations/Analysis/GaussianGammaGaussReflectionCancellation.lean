import IPRADerivations.Analysis.GaussianGammaGaussReferencePrefix
import IPRADerivations.Analysis.GaussianCyclicSineProductRatio

/-!
# Canceling the explicit nonzero sine normalization factor

The literal M1 ratio `(N+1)/2^N` has the literal rational inverse
`2^N/(N+1)`. Canceling it in a cleared named identity preserves the
original product names and requires only their regularity.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionCancellation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode mul)
open GaussianCyclicSineProductRatio (ratio)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianGammaEncodingRescaling (one_constant_cross)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (oneF one_fast multiply_associative multiply_one)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_refl)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalHorner (qmul qmul_canonical qmul_represents represents_congr canonical_unique
  ofGaussian ofGaussian_represents positive_product)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRationalSyntheticDivision (qone_canonical)
open GaussianRationalNaturalScale (natural_product_value)
open GaussianRootAlgebra (equal equal_of_values equal_trans re_scale im_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inverseRatio (N : PTm n) : PTm n := ofGaussian (scale (unit N) oneCode) (succ N)

@[simp] theorem subst_inverseRatio {l : ℕ} (σ : Fin n → PTm l) (N : PTm n) :
    Syn.subst σ (inverseRatio N) = inverseRatio (Syn.subst σ N) := by
  simp [inverseRatio,oneCode]

theorem ratio_product (N : PTm n) : Γ ⊢[PRAAx] qmul (ratio N) (inverseRatio N) ≐ qone := by
  let m := succ N
  let u := unit N
  have hm := zero_lt_succ (Γ := Γ) N
  have hu := unit_positive (Γ := Γ) N
  have value : Γ ⊢[PRAAx] equal (mul (scale m oneCode) (scale u oneCode)) (scale (u*m) oneCode) := by
    apply equal_trans (natural_product_value m (scale u oneCode))
    apply equal_of_values <;> simp only [re_scale,im_scale] <;> ipra_simps <;> ring
  have h := qmul_represents (ratio N) (inverseRatio N) (scale m oneCode) (scale u oneCode) u m hu hm
    (ofGaussian_represents _ _ hu) (ofGaussian_represents _ _ hm)
  exact canonical_unique _ _ _ (u*m) (qmul_canonical _ _) qone_canonical (positive_product _ _ hu hm)
    (represents_congr (.eqRefl _) value (.eqRefl _) h) (qone_represents_scaled _)

theorem cancel_right_constant (f g : PR 2) (x y a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hunit : Γ ⊢[PRAAx] qmul a b ≐ qone)
    (h : Γ ⊢[PRAAx] crossEquivalent (multiplyF f constantF) g (multiplyData f constantF x a) y) :
    Γ ⊢[PRAAx] crossEquivalent f (multiplyF g constantF) x (multiplyData g constantF y b) := by
  let C := constantF
  let d := multiplyData f C x a
  let e := multiplyData C C a b
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have hD := multiply_fast f C x a hf ha
  have hE := multiply_fast C C a b ha hb
  have p := multiply_cross (multiplyF f C) g C C d y b b hD hg hb hb h (cross_refl _ _ hb)
  have uv := cross_trans _ _ _ _ _ _ (constant_product_cross a b) (constant_data_cross _ _ hunit)
  have v := cross_trans _ _ _ _ _ _ uv
    (cross_symm _ _ _ _
      (cross_trans _ _ _ _ _ _ (GaussianBoundedInverseApartness.ones_equivalent x zero) one_constant_cross))
  have w := multiply_cross f f (multiplyF C C) oneF x x e x hf hf hE (one_fast x)
    (cross_refl _ _ hf) v
  have q := cross_trans _ _ _ _ _ _ (multiply_associative f C C x a b hf ha hb)
    (cross_trans _ _ _ _ _ _ w (multiply_one f x hf))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ q) p

theorem cancel_sine_ratio (f g : PR 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (h : Γ ⊢[PRAAx] crossEquivalent (multiplyF f constantF) g (multiplyData f constantF x (ratio N)) y) :
    Γ ⊢[PRAAx] crossEquivalent f (multiplyF g constantF) x (multiplyData g constantF y (inverseRatio N)) :=
  cancel_right_constant f g x y (ratio N) (inverseRatio N) hf hg (ratio_product N) h

theorem actual_Gauss_sine_ratio_cancellation_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((pointCN f (var 1) ⋏ pointCN g (var 0)) ⟶
        crossEquivalent (multiplyF f constantF) g (multiplyData f constantF (var 1) (ratio (var 2))) (var 0) ⟶
        crossEquivalent f (multiplyF g constantF) (var 1) (multiplyData g constantF (var 0) (inverseRatio (var 2)))) :=
  closeUniv 3 (.impI (.impI (cancel_sine_ratio f g _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionCancellation
