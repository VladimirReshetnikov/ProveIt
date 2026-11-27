import IPRADerivations.Analysis.Gamma.FunctionalEquations.ReciprocalGamma.GaussianGammaAdjacentCutoff
import IPRADerivations.Analysis.Gamma.Names.Input.GaussianGammaEncodingRescaling
import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameRingLaws

/-!
# Squares and units of actual named products
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianNamedProductSquare

open_ipra
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameRingLaws (multiply_associative multiply_commutative multiply_one oneF one_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalReciprocal (qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem square_product (f g : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hg : Γ ⊢[PRAAx] pointCN g y) :
    Γ ⊢[PRAAx] crossEquivalent
      (multiplyF (multiplyF f g) (multiplyF f g)) (multiplyF (multiplyF f f) (multiplyF g g))
      (multiplyData (multiplyF f g) (multiplyF f g) (multiplyData f g x y) (multiplyData f g x y))
      (multiplyData (multiplyF f f) (multiplyF g g) (multiplyData f f x x) (multiplyData g g y y)) := by
  let A := multiplyF f g
  let B := multiplyF g f
  let C := multiplyF f f
  let a := multiplyData f g x y
  let b := multiplyData g f y x
  let c := multiplyData f f x x
  have ha := multiply_fast f g x y hf hg
  have hb := multiply_fast g f y x hg hf
  have hc := multiply_fast f f x x hf hf
  have ab : Γ ⊢[PRAAx] crossEquivalent (multiplyF A f) (multiplyF f B)
      (multiplyData A f a x) (multiplyData f B x b) :=
    multiply_associative f g f x y x hf hg hf
  have ba : Γ ⊢[PRAAx] crossEquivalent (multiplyF f B) (multiplyF f A)
      (multiplyData f B x b) (multiplyData f A x a) :=
    multiply_cross f f B A x x b a hf hf hb ha (cross_refl _ _ hf) (multiply_commutative g f y x hg hf)
  have ac : Γ ⊢[PRAAx] crossEquivalent (multiplyF f A) (multiplyF C g)
      (multiplyData f A x a) (multiplyData C g c y) :=
    cross_symm _ _ _ _ (multiply_associative f f g x x y hf hf hg)
  have rewrite := multiply_cross (multiplyF A f) (multiplyF C g) g g
    (multiplyData A f a x) (multiplyData C g c y) y y
    (multiply_fast A f a x ha hf) (multiply_fast C g c y hc hg) hg hg
    (cross_trans _ _ _ _ _ _ ab (cross_trans _ _ _ _ _ _ ba ac)) (cross_refl _ _ hg)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative A f g a x y ha hf hg))
    (cross_trans _ _ _ _ _ _ rewrite (multiply_associative C g g c y y hc hg hg))

theorem right_unit (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f constantF) f (multiplyData f constantF x qone) x := by
  have eq : Γ ⊢[PRAAx] crossEquivalent oneF constantF x qone :=
    cross_trans _ _ _ _ _ _ (GaussianBoundedInverseApartness.ones_equivalent x zero)
      GaussianGammaEncodingRescaling.one_constant_cross
  have e := multiply_cross f f constantF oneF x x qone x hf hf (constant_regular _) (one_fast x)
    (cross_refl _ _ hf) (cross_symm _ _ _ _ eq)
  exact cross_trans _ _ _ _ _ _ e (multiply_one f x hf)

theorem left_unit (f : PR 2) (x : PTm n) (hf : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF f) f (multiplyData constantF f qone x) x :=
  cross_trans _ _ _ _ _ _ (multiply_commutative constantF f qone x (constant_regular _) hf) (right_unit f x hf)

end LeanProofs.IPRA.Analysis.GaussianNamedProductSquare
