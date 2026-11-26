import IPRADerivations.Analysis.Names.Rates.Perturbations.GaussianNamedSmallPerturbationTransport
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.GaussianRationalLowerBounds

/-!
# Apartness of an actual product of regular names

The two input apartness certificates supply late rational lower bounds.
Reading both names at the original multiplication clock gives their
product lower bound at one explicit precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedProductApartness

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameReciprocal (lower apart anchor lower_congr R tail_lower R_positive)
open GaussianNamedSmallPerturbationTransport (productClock product_at)
open GaussianNameArithmetic (multiplyF multiplyData)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def height (a b : PTm n) : PTm n := succ a+succ b

theorem late_lower (f : PR 2) (a x p : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (ha : Γ ⊢[PRAAx] apart f a x)
    (hp : Γ ⊢[PRAAx] le (anchor a) p) :
    Γ ⊢[PRAAx] lower (ap2 f p x) (R a) := by
  let s := monus p (anchor a)
  have e : Γ ⊢[PRAAx] p ≐ s+anchor a := (eq_add_of_le hp).eqTrans (add_comm _ _)
  exact lower_congr (congrAp2 f e.eqSymm (.eqRefl _)) (.eqRefl _) (tail_lower f a x s hf ha)

theorem original_apart (f g : PR 2) (x y a b : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (ha : Γ ⊢[PRAAx] apart f a x) (hb : Γ ⊢[PRAAx] apart g b y) :
    Γ ⊢[PRAAx] apart (multiplyF f g) (height a b) (multiplyData f g x y) := by
  let H := height a b
  let p := anchor H
  let t := productClock f g x y p
  have hat : Γ ⊢[PRAAx] le (anchor a) t :=
    le_trans (add_le_add_right two (le_trans (le_succ_self a) (le_add_right (succ a) (succ b))))
      (le_add_right _ _)
  have hbt : Γ ⊢[PRAAx] le (anchor b) t :=
    le_trans (add_le_add_right two (le_trans (le_succ_self b) (le_add_left (succ b) (succ a))))
      (le_add_right _ _)
  have actual := GaussianRationalLowerBounds.product_lower (ap2 f t x) (ap2 g t y) one (R a) one (R b)
    (R_positive a) (R_positive b) (late_lower f a x t hf ha hat) (late_lower g b y t hg hb hbt)
  have pay : Γ ⊢[PRAAx] R a*R b ≐ unit H := (pw_add two (succ a) (succ b)).eqSymm
  exact GaussianRationalLowerBounds.lower_congr (product_at f g x y p).eqSymm (one_mul one) pay actual

theorem actual_named_product_apart_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((pointCN f (var 0) ⋏ pointCN g (var 1)) ⋏ (apart f (var 2) (var 0) ⋏ apart g (var 3) (var 1)) ⟶
      apart (multiplyF f g) (height (var 2) (var 3)) (multiplyData f g (var 0) (var 1))) :=
  closeUniv 4 (.impI (original_apart f g _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedProductApartness
