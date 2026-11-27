import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamily

/-!
# Congruence for products of finite Gaussian families

Rowwise equivalence at independent precisions implies equivalence
of the actual products. Each side keeps the radius and query
normalizer computed from its original family.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamilyCongruence

open_ipra
open GaussianCoefficientNameBounds (unit)
open GaussianNamedFiniteProduct (rowDistance amplification)
open GaussianNamedFiniteProductFamily (rowF row_at regularRows radius productData family_bounds family_regular)
open GaussianNamedFiniteProductName (nameF rowBounds cofinalRows cofinal_raw raw_regular)
open GaussianNameEquivalence (crossEquivalent cross_diagonal_at)
open GaussianRationalDistanceOrder (distance_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def equalRows (f g : PR 2) (t u : PTm 2) (N x y : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶
    crossEquivalent f g (inst2 t (var 0) (Syn.shift x)) (inst2 u (var 0) (Syn.shift y)))

ipra_subst equalRows [Syn.subst_shift, Syn.shift_subst]

theorem equal_at (f g : PR 2) (t u : PTm 2) (N x y i : PTm n)
    (h : Γ ⊢[PRAAx] equalRows f g t u N x y) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] crossEquivalent f g (inst2 t i x) (inst2 u i y) := by
  have e : Γ ⊢[PRAAx] lt i N ⟶ crossEquivalent f g (inst2 t i x) (inst2 u i y) := by
    simpa [equalRows] using h.allE i
  exact .impE e hi

theorem row_rate (f g : PR 2) (t u : PTm 2) (N x y : PTm n) (h : Γ ⊢[PRAAx] equalRows f g t u N x y) :
    Γ ⊢[PRAAx] cofinalRows (rowF f t) (rowF g u) N two x y := by
  refine .allI (.allI (.impI ?_))
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := lt (var 0) (sh N) :: (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let i : PTm (n+2) := var 0
  let X := inst2 t i (sh x)
  let Y := inst2 u i (sh y)
  have hs : Δ ⊢[PRAAx] equalRows f g t u (sh N) (sh x) (sh y) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift.wk
  have rate := cross_diagonal_at p (equal_at f g t u (sh N) (sh x) (sh y) i hs Prf.hyp0)
  simpa [cofinalRows,rowDistance,Syn.shift,sh,Δ,p,i,X,Y,two,one] using
    distance_congr (row_at f t p i (sh x)).eqSymm (row_at g u p i (sh y)).eqSymm (.eqRefl _) (.eqRefl _) rate

theorem row_bounds_widen (f : PR 3) (N R S x : PTm n) (h : Γ ⊢[PRAAx] rowBounds f N R x)
    (hr : Γ ⊢[PRAAx] le R S) : Γ ⊢[PRAAx] rowBounds f N S x :=
  GaussianNamedFiniteProductName.row_bounds_mono f N N R S x h (le_refl N) hr

theorem family_product_cross (f g : PR 2) (t u : PTm 2) (N x y : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N y)
    (h : Γ ⊢[PRAAx] equalRows f g t u N x y) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (rowF f t)) (nameF (rowF g u))
      (productData f t N x) (productData g u N y) := by
  let F := rowF f t
  let G := rowF g u
  let R := radius f t N x
  let S := radius g u N y
  have bF := family_bounds f t N x hf
  have bG := family_bounds g u N y hg
  have rF := raw_regular F N R one x bF (family_regular f t N x hf)
  have rG := raw_regular G N S one y bG (family_regular g u N y hg)
  have rate := cofinal_raw F G N (R+S) two x y
    (row_bounds_widen F N R (R+S) x bF (le_add_right R S))
    (row_bounds_widen G N S (R+S) y bG (le_add_left S R)) (row_rate f g t u N x y h)
  exact GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ _ rF rG rate

theorem actual_family_product_cross_closed (f g : PR 2) (t u : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((regularRows f t (var 0) (var 1) ⋏ regularRows g u (var 0) (var 2)) ⟶
        equalRows f g t u (var 0) (var 1) (var 2) ⟶
        crossEquivalent (nameF (rowF f t)) (nameF (rowF g u))
          (productData f t (var 0) (var 1)) (productData g u (var 0) (var 2))) :=
  closeUniv 3 (.impI (.impI (family_product_cross f g t u _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamilyCongruence
