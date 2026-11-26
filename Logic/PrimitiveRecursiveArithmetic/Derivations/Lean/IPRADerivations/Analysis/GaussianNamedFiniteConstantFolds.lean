import IPRADerivations.Analysis.GaussianNamedFiniteSumFamily
import IPRADerivations.Analysis.GaussianNameConjugation
import IPRADerivations.Analysis.GaussianGammaCanonicalExponent

/-!
# Literal finite sums and products of Gaussian constant names

Every observation returns the underlying rational fold. Clock changes
made by both original named folds leave their constant rows unchanged.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteConstantFolds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameConjugation (equal_samples_cross pointwiseEqual)
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProductFamily (regularRows rowF row_at productData family_product_regular)
open GaussianRationalFiniteProduct (qprod product_congr_bounded)
open GaussianRationalFiniteSum (termsEqual)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "rsum" => GaussianRationalFiniteSum.sum

theorem rows_regular (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] regularRows constantF t N x :=
  .allI (.impI (constant_regular _))

theorem sum_sample (t : PTm 2) (p N x : PTm n) : Γ ⊢[PRAAx] ap2 (GaussianNamedFiniteSumFamily.nameF constantF t) p (GaussianNamedFiniteSumFamily.data N x) ≐ rsum t N x := by
  let s := GaussianFastValueCut.exponent N p
  refine (GaussianNamedFiniteSumFamily.sample_at constantF t p N x).eqTrans ?_
  change Γ ⊢[PRAAx] rsum (GaussianNamedFiniteSumFamily.body constantF t) N (pairT s x) ≐ rsum t N x
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  simpa only [Syn.shift,subst_pairT] using
    (GaussianNamedFiniteSumFamily.term_at constantF t (var 0) (Syn.shift s) (Syn.shift x)).eqTrans (constant_at _ _)

theorem product_sample (t : PTm 2) (p N x : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianNamedFiniteProductName.nameF (rowF constantF t)) p (productData constantF t N x) ≐ qprod t N x := by
  let f := rowF constantF t
  let T := GaussianNamedFiniteProduct.body f
  let R := GaussianNamedFiniteProductFamily.radius constantF t N x
  let s := GaussianNamedFiniteProductName.clock N R one p
  refine (GaussianNamedFiniteProductName.name_at f p N R one x).eqTrans ?_
  change Γ ⊢[PRAAx] qprod (GaussianRationalRectangularProduct.rowBody T) N (pairT s x) ≐ qprod t N x
  apply product_congr_bounded
  refine .allI (.impI ?_)
  have a := GaussianRationalRectangularProduct.row_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) T
    (Syn.shift s) (var 0) (Syn.shift x)
  have a' : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
      inst2 (GaussianRationalRectangularProduct.rowBody T) (var 0) (pairT (Syn.shift s) (Syn.shift x)) ≐
        ap3 (rowF constantF t) (Syn.shift s) (var 0) (Syn.shift x) := by
    simpa [T,f,GaussianNamedFiniteProduct.body,inst3] using a
  have b := row_at (Γ := lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) constantF t
    (Syn.shift s) (var 0) (Syn.shift x)
  simpa only [Syn.shift,subst_pairT] using a'.eqTrans (b.eqTrans (constant_at _ _))

theorem sum_cross (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedFiniteSumFamily.nameF constantF t) constantF (GaussianNamedFiniteSumFamily.data N x) (rsum t N x) := by
  apply equal_samples_cross _ _ _ _ (GaussianNamedFiniteSumFamily.regular constantF t N x (rows_regular t N x)) (constant_regular _)
  refine .allI ?_
  simpa only [pointwiseEqual,Syn.shift,GaussianNamedFiniteSumFamily.subst_data,GaussianRationalFiniteSum.subst_sum] using
    (sum_sample (Γ := Γ.map Fm.shift) t (var 0) (Syn.shift N) (Syn.shift x)).eqTrans (constant_at _ _).eqSymm

theorem product_cross (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF constantF t)) constantF (productData constantF t N x) (qprod t N x) := by
  apply equal_samples_cross _ _ _ _ (family_product_regular constantF t N x (rows_regular t N x)) (constant_regular _)
  refine .allI ?_
  have data_shift : Syn.shift (productData constantF t N x) = productData constantF t (Syn.shift N) (Syn.shift x) := by
    simp [Syn.shift,productData,one]
  change (Γ.map Fm.shift) ⊢[PRAAx] ap2 (GaussianNamedFiniteProductName.nameF (rowF constantF t)) (var 0)
    (Syn.shift (productData constantF t N x)) ≐ ap2 constantF (var 0) (Syn.shift (qprod t N x))
  rw [data_shift]
  simpa only [Syn.shift,GaussianRationalFiniteProduct.subst_qprod] using
    (product_sample (Γ := Γ.map Fm.shift) t (var 0) (Syn.shift N) (Syn.shift x)).eqTrans (constant_at (var 0) _).eqSymm

theorem actual_named_constant_folds_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent (GaussianNamedFiniteSumFamily.nameF constantF t) constantF (GaussianNamedFiniteSumFamily.data (var 0) (var 1)) (rsum t (var 0) (var 1)) ⋏
      crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF constantF t)) constantF (productData constantF t (var 0) (var 1)) (qprod t (var 0) (var 1))) :=
  closeUniv 2 (.andI (sum_cross t _ _) (product_cross t _ _))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteConstantFolds
