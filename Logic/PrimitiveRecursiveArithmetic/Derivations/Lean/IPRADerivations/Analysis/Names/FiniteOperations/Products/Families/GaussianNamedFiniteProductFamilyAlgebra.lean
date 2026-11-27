import IPRADerivations.Analysis.Names.FiniteOperations.Products.Identities.GaussianNamedFiniteProductAlgebra
import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamilyCongruence

/-!
# Products of rowwise multiplications of Gaussian names

The rowwise multiplication and both operand products use independent
precision clocks. A uniform comparison to the raw rational row products
identifies the product of the named rows with the multiplication of
the two named products.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamilyAlgebra

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedFiniteProductAlgebra (rowProduct product_row_bounds product_row_regular named_product)
open GaussianNamedFiniteProductFamily (rowF row_at regularRows regular_at radius productData family_radius_at
  family_bounds family_regular)
open GaussianNamedFiniteProductFamilyCongruence (row_bounds_widen)
open GaussianNamedFiniteProductName (nameF data cofinalRows rowBounds rowRegular raw_regular cofinal_raw)
open GaussianNamedFiniteProduct (rowDistance)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono_same)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def multiplyBody (f g : PR 2) (t u : PTm 2) : PTm 2 := multiplyData f g t u

theorem body_at (f g : PR 2) (t u : PTm 2) (i x : PTm n) :
    inst2 (multiplyBody f g t u) i x = multiplyData f g (inst2 t i x) (inst2 u i x) := by
  simp only [multiplyBody, inst2, GaussianNameArithmetic.subst_multiplyData]

theorem multiply_regular (f g : PR 2) (t u : PTm 2) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] regularRows (multiplyF f g) (multiplyBody f g t u) N x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift
  have hF : Δ ⊢[PRAAx] regularRows f t (Syn.shift N) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift, Δ] using hf.shift.wk
  have hG : Δ ⊢[PRAAx] regularRows g u (Syn.shift N) (Syn.shift x) := by
    simpa [Fm.shift, Syn.shift, Δ] using hg.shift.wk
  simp only [body_at]
  exact multiply_fast f g _ _ (regular_at f t _ _ _ hF Prf.hyp0)
    (regular_at g u _ _ _ hG Prf.hyp0)

def rowBudget (f g : PR 2) (t u : PTm 2) (N x : PTm n) : PTm n :=
  radius f t N x+radius g u N x+one

theorem row_comparison (f g : PR 2) (t u : PTm 2) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] cofinalRows (rowF (multiplyF f g) (multiplyBody f g t u)) (rowProduct (rowF f t) (rowF g u))
      N (rowBudget f g t u N x) x (pairT x x) := by
  refine .allI (.allI (.impI ?_))
  let sh := fun z : PTm n => Syn.shift (Syn.shift z)
  let Δ := lt (var 0) (sh N) :: (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let i : PTm (n+2) := var 0
  let X := inst2 t i (sh x)
  let Y := inst2 u i (sh x)
  have hi : Δ ⊢[PRAAx] lt i (sh N) := Prf.hyp0
  have hF : Δ ⊢[PRAAx] regularRows f t (sh N) (sh x) := by
    simpa [Fm.shift, Syn.shift, sh, Δ] using hf.shift.shift.wk
  have hG : Δ ⊢[PRAAx] regularRows g u (sh N) (sh x) := by
    simpa [Fm.shift, Syn.shift, sh, Δ] using hg.shift.shift.wk
  have h := GaussianNameRingLaws.multiply_sample_error f g X Y p
    (regular_at f t _ _ _ hF hi) (regular_at g u _ _ _ hG hi)
  have b : Δ ⊢[PRAAx] le (multiplyModulus f g X Y+one) (rowBudget f g t u (sh N) (sh x)) :=
    add_le_add₂ (add_le_add₂ (family_radius_at f t _ _ _ hi) (family_radius_at g u _ _ _ hi)) (le_refl one)
  have left := row_at (Γ := Δ) (multiplyF f g) (multiplyBody f g t u) p i (sh x)
  rw [body_at] at left
  have right := (GaussianNamedFiniteProductAlgebra.row_at (Γ := Δ) (rowF f t) (rowF g u) p i (sh x) (sh x)).eqTrans
    (qmul_congr (row_at f t p i (sh x)) (row_at g u p i (sh x)))
  simpa [cofinalRows, rowDistance, rowBudget, Syn.shift, sh, Δ, X, Y, i, p, one] using
    distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _)
      (distance_radius_mono_same (unit_positive p) b h)

theorem family_multiply_cross (f g : PR 2) (t u : PTm 2) (N x : PTm n)
    (hf : Γ ⊢[PRAAx] regularRows f t N x) (hg : Γ ⊢[PRAAx] regularRows g u N x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF (rowF (multiplyF f g) (multiplyBody f g t u)))
      (multiplyF (nameF (rowF f t)) (nameF (rowF g u)))
      (productData (multiplyF f g) (multiplyBody f g t u) N x)
      (multiplyData (nameF (rowF f t)) (nameF (rowF g u)) (productData f t N x) (productData g u N x)) := by
  let F := rowF f t
  let G := rowF g u
  let H := rowF (multiplyF f g) (multiplyBody f g t u)
  let K := rowProduct F G
  let R := radius f t N x
  let S := radius g u N x
  let T := radius (multiplyF f g) (multiplyBody f g t u) N x
  let Y := pairT x x
  have bF := family_bounds f t N x hf
  have bG := family_bounds g u N x hg
  have rF := family_regular f t N x hf
  have rG := family_regular g u N x hg
  have hH := multiply_regular f g t u N x hf hg
  have bH : Γ ⊢[PRAAx] rowBounds H N T x := family_bounds _ _ _ _ hH
  have bK : Γ ⊢[PRAAx] rowBounds K N (R*S) Y := product_row_bounds F G N R S x x bF bG
  have rH : Γ ⊢[PRAAx] rowRegular H N one x := family_regular _ _ _ _ hH
  have rK : Γ ⊢[PRAAx] rowRegular K N (one*S+R*one) Y := product_row_regular F G N R S one one x x bF bG rF rG
  have rate := cofinal_raw H K N (T+R*S) (rowBudget f g t u N x) x Y
    (row_bounds_widen H N T (T+R*S) x bH (le_add_right T (R*S)))
    (row_bounds_widen K N (R*S) (T+R*S) Y bK (le_add_left (R*S) T)) (row_comparison f g t u N x hf hg)
  have agree := GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ _
    (raw_regular H N T one x bH rH) (raw_regular K N (R*S) (one*S+R*one) Y bK rK) rate
  exact cross_trans _ _ _ _ _ _ agree (named_product F G N R S one one x x bF bG rF rG)

theorem actual_family_multiply_closed (f g : PR 2) (t u : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((regularRows f t (var 0) (var 1) ⋏ regularRows g u (var 0) (var 1)) ⟶
        crossEquivalent (nameF (rowF (multiplyF f g) (multiplyBody f g t u)))
          (multiplyF (nameF (rowF f t)) (nameF (rowF g u)))
          (productData (multiplyF f g) (multiplyBody f g t u) (var 0) (var 1))
          (multiplyData (nameF (rowF f t)) (nameF (rowF g u))
            (productData f t (var 0) (var 1)) (productData g u (var 0) (var 1)))) :=
  closeUniv 2 (.impI (family_multiply_cross f g t u _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductFamilyAlgebra
