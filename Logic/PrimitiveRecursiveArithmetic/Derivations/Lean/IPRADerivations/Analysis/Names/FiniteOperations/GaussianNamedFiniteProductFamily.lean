import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductName

/-!
# A product of a finite family of original Gaussian names

Each index has its own program input and a proof of regularity.
Their original radius bounds sum to a single computed bound for
all rows, which suffices to construct the named product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamily

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameBounds (U sample_bound)
open GaussianNameEquivalence (point_at)
open GaussianNamedFiniteProduct (rowBoundsAt rowDistance)
open GaussianNamedFiniteProductName (nameF data rowBounds rowRegular name_regular)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalReciprocal (bound_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowF (f : PR 2) (t : PTm 2) : PR 3 :=
  PTm.toPR (ap2 f (var 0) (inst2 t (var 1) (var 2)) : PTm 3)

theorem row_at (f : PR 2) (t : PTm 2) (p i x : PTm n) :
    Γ ⊢[PRAAx] ap3 (rowF f t) p i x ≐ ap2 f p (inst2 t i x) := by
  simpa [rowF,ap3] using toPR_eq (Γ := Γ) (ap2 f (var 0) (inst2 t (var 1) (var 2)) : PTm 3) ![p,i,x]

def regularRows (f : PR 2) (t : PTm 2) (N x : PTm n) : Fm PTm n :=
  .all (lt (var 0) (Syn.shift N) ⟶ pointCN f (inst2 t (var 0) (Syn.shift x)))

ipra_subst regularRows [Syn.subst_shift, Syn.shift_subst]

def radiusBody (f : PR 2) (t : PTm 2) : PTm 2 := U f t
def radius (f : PR 2) (t : PTm 2) (N x : PTm n) : PTm n := ap2 (sumF (radiusBody f t)) N x
def productData (f : PR 2) (t : PTm 2) (N x : PTm n) : PTm n := data N (radius f t N x) one x

ipra_subst radius

theorem regular_at (f : PR 2) (t : PTm 2) (N x i : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t N x) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] pointCN f (inst2 t i x) := by
  have next : Γ ⊢[PRAAx] lt i N ⟶ pointCN f (inst2 t i x) := by simpa [regularRows] using h.allE i
  exact .impE next hi

theorem family_radius_at (f : PR 2) (t : PTm 2) (N x i : PTm n) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (U f (inst2 t i x)) (radius f t N x) := by
  simpa [inst2,radiusBody,radius] using term_le_sum (radiusBody f t) (x := x) hi

theorem family_bounds (f : PR 2) (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] rowBounds (rowF f t) N (radius f t N x) x := by
  refine .allI (.allI (.impI ?_))
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := lt (var 0) (sh N) :: (Γ.map Fm.shift).map Fm.shift
  let r := inst2 t (var 0) (sh x)
  have hs : Δ ⊢[PRAAx] regularRows f t (sh N) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift.wk
  have src := regular_at f t (sh N) (sh x) (var 0) hs Prf.hyp0
  have b := sample_bound f r (var 1) src
  have e := mul_le_mul_right one (family_radius_at f t (sh N) (sh x) (var 0) (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (sh N)))
  simpa [rowBounds,rowBoundsAt,Syn.shift,sh,Δ] using
    bound_congr (row_at f t (var 1) (var 0) (sh x)).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) e b)

theorem family_regular (f : PR 2) (t : PTm 2) (N x : PTm n) (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] rowRegular (rowF f t) N one x := by
  refine .allI (.allI (.allI (.impI ?_)))
  let sh := fun t : PTm n => Syn.shift (Syn.shift (Syn.shift t))
  let Δ := lt (var 0) (sh N) :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f t (sh N) (sh x) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.shift.shift.wk
  have src := regular_at f t (sh N) (sh x) (var 0) hs Prf.hyp0
  simpa [rowRegular,rowDistance,Syn.shift,sh,Δ,one] using
    distance_congr (row_at f t (var 2) (var 0) (sh x)).eqSymm (row_at f t (var 1) (var 0) (sh x)).eqSymm
      (one_mul (unit (var 2)+unit (var 1))).eqSymm (.eqRefl _)
      (point_at f (inst2 t (var 0) (sh x)) (var 2) (var 1) src)

theorem family_product_regular (f : PR 2) (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f t N x) :
    Γ ⊢[PRAAx] pointCN (nameF (rowF f t)) (productData f t N x) :=
  name_regular _ _ _ _ _ (family_bounds f t N x h) (family_regular f t N x h)

theorem actual_regular_family_product_closed (f : PR 2) (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (regularRows f t (var 0) (var 1) ⟶ pointCN (nameF (rowF f t)) (productData f t (var 0) (var 1))) :=
  closeUniv 2 (.impI (family_product_regular f t _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamily
