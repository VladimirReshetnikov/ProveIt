import IPRADerivations.Analysis.Names.FiniteOperations.Products.Families.GaussianNamedFiniteProductFamily
import IPRADerivations.Analysis.Gamma.EulerProducts.Weierstrass.GaussianGammaWeierstrassApproximant
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.GaussianRationalFiniteProduct

/-!
# Products of finite families of constant Gaussian names

The normalized finite name product has the same value as the literal
rational fold, at every precision and every internal family size.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedConstantFamilyProduct

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianNamedFiniteProductFamily (rowF row_at productData radius regularRows)
open GaussianNamedFiniteProductName (nameF name_at clock)
open GaussianRationalFiniteProduct (qprod product_zero product_succ)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem constant_rows_regular (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx] regularRows constantF t N x :=
  .allI (.impI (constant_regular _))

private def sampleLaw (t : PTm 2) (p N x : PTm n) : Fm PTm n :=
  sample (rowF constantF t) p N x ≐ qprod t N x

@[simp] private theorem subst_sampleLaw {l : ℕ} (σ : Fin n → PTm l) (t : PTm 2) (p N x : PTm n) :
    (sampleLaw t p N x).subst σ = sampleLaw t (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ x) := by
  simp [sampleLaw]

theorem sample_equals_fold (t : PTm 2) (p N x : PTm n) :
    Γ ⊢[PRAAx] sample (rowF constantF t) p N x ≐ qprod t N x := by
  have all : Γ ⊢[PRAAx] .all (sampleLaw t (Syn.shift p) (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_sampleLaw]
    · exact (sample_zero _ _ _).eqTrans (product_zero _ _).eqSymm
    · exact (sample_succ _ _ _ _).eqTrans
        ((qmul_congr Prf.hyp0 ((row_at constantF t _ _ _).eqTrans (constant_at _ _))).eqTrans
          (product_succ _ _ _).eqSymm)
  have result : Γ ⊢[PRAAx] sampleLaw t p N x := by
    simpa only [subst_sampleLaw, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] using all.allE N
  exact result

theorem name_equals_fold (t : PTm 2) (p N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF (rowF constantF t)) p (productData constantF t N x) ≐ qprod t N x :=
  (name_at _ _ _ _ _ _).eqTrans (sample_equals_fold t (clock N (radius constantF t N x) one p) N x)

theorem constant_product_cross (t : PTm 2) (N x : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (nameF (rowF constantF t)) constantF (productData constantF t N x) (qprod t N x) := by
  let sh (a : PTm n) := Syn.shift (Syn.shift a)
  let a := qprod t N x
  apply GaussianNameEquivalence.transport_by_sample_eq (cross_refl constantF a (constant_regular a))
  · simpa [Syn.shift, sh, a, productData, one] using
      (name_equals_fold t (var 1) (sh N) (sh x)).eqTrans (constant_at (var 1) (qprod t (sh N) (sh x))).eqSymm
  · exact .eqRefl _

theorem actual_constant_family_product_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (crossEquivalent (nameF (rowF constantF t)) constantF
      (productData constantF t (var 0) (var 1)) (qprod t (var 0) (var 1))) :=
  closeUniv 2 (constant_product_cross t _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedConstantFamilyProduct
