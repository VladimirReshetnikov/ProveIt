import IPRADerivations.Analysis.Gamma.EulerProducts.Gauss.GaussianGaussEulerInverseHeadGrouping
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedConstantFamilyProduct

/-!
# The exact Gauss inverse-head identity on the named products

Each finite product of constant inverse-head names evaluates to the
corresponding canonical rational fold. The exact rational equality
therefore also identifies the two named products at independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerNamedHeadGrouping

open_ipra
open ComplexLogarithmRemainder (oneCode scale)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaEulerDenominatorGrouping (shiftedData)
open GaussianGammaEulerFullHeadInverse (headInverse)
open GaussianGammaGaussEulerHeads (cutoff)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGaussEulerInverseHeadGrouping (shiftedInverseBody referenceInverseBody shiftedInverses referenceInverses inverse_grouping)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast recode_congr)
open GaussianNameEquivalence (crossEquivalent cross_at cross_refl cross_symm cross_trans)
open GaussianNamedConstantFamilyProduct (constant_rows_regular constant_product_cross)
open GaussianNamedFiniteProductFamily (rowF productData family_product_regular)
open GaussianNamedFiniteProductName (nameF)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul qmul_canonical)

variable {n : ℕ} {Γ : List (Fm PTm n)}

abbrev shiftedNameF : PR 2 := nameF (rowF constantF shiftedInverseBody)
abbrev referenceNameF : PR 2 := nameF (rowF constantF referenceInverseBody)
def shiftedNameData (z B m N : PTm n) : PTm n := productData constantF shiftedInverseBody m (shiftedData z B m N)
def referenceNameData (m N : PTm n) : PTm n := productData constantF referenceInverseBody m (pairT m N)

ipra_subst shiftedNameData [productData, one]

ipra_subst referenceNameData [productData, one]

theorem shifted_regular (z B m N : PTm n) : Γ ⊢[PRAAx] pointCN shiftedNameF (shiftedNameData z B m N) :=
  family_product_regular _ _ _ _ (constant_rows_regular _ _ _)

theorem reference_regular (m N : PTm n) : Γ ⊢[PRAAx] pointCN referenceNameF (referenceNameData m N) :=
  family_product_regular _ _ _ _ (constant_rows_regular _ _ _)

private theorem constant_binary_sample (p x y : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF constantF constantF) p (multiplyData constantF constantF x y) ≐ qmul x y :=
  (GaussianGammaReciprocalInverse.constant_product_sample p x y).eqTrans
    (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))

private theorem constant_binary_cross (x y u v : PTm n) (h : Γ ⊢[PRAAx] qmul x y ≐ qmul u v) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF constantF) (multiplyF constantF constantF)
      (multiplyData constantF constantF x y) (multiplyData constantF constantF u v) := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (w : PTm n) := Syn.shift (Syn.shift w)
  let F := multiplyF constantF constantF
  let right := multiplyData constantF constantF (sh u) (sh v)
  have hs : Δ ⊢[PRAAx] qmul (sh x) (sh y) ≐ qmul (sh u) (sh v) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using h.shift.shift
  have e := (constant_binary_sample (var 1) (sh x) (sh y)).eqTrans
    (hs.eqTrans (constant_binary_sample (var 1) (sh u) (sh v)).eqSymm)
  have hr : Δ ⊢[PRAAx] pointCN F right :=
    multiply_fast constantF constantF (sh u) (sh v) (constant_regular _) (constant_regular _)
  have step := distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (cross_at F F right right (var 1) (var 0) (cross_refl F right hr))
  simpa only [crossEquivalent,Δ,sh,F,right,GaussianNameArithmetic.subst_multiplyData,Syn.shift] using step

theorem named_head_grouping (z R B m a d N : PTm n) (h : Γ ⊢[PRAAx] source z R B m a d) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF shiftedNameF constantF) (multiplyF constantF referenceNameF)
      (multiplyData shiftedNameF constantF (shiftedNameData z B m N) (headInverse oneCode one (cutoff m N)))
      (multiplyData constantF referenceNameF (headInverse (scale m z) B (cutoff m N)) (referenceNameData m N)) := by
  let L := cutoff m N
  let u := headInverse oneCode one L
  let v := headInverse (scale m z) B L
  let s := shiftedInverses z B m N
  let r := referenceInverses m N
  have hs : Γ ⊢[PRAAx] crossEquivalent shiftedNameF constantF (shiftedNameData z B m N) s :=
    constant_product_cross shiftedInverseBody m (shiftedData z B m N)
  have hr : Γ ⊢[PRAAx] crossEquivalent referenceNameF constantF (referenceNameData m N) r :=
    constant_product_cross referenceInverseBody m (pairT m N)
  have left := multiply_cross shiftedNameF constantF constantF constantF (shiftedNameData z B m N) s u u
    (shifted_regular z B m N) (constant_regular s) (constant_regular u) (constant_regular u)
    hs (cross_refl _ _ (constant_regular u))
  have right := multiply_cross constantF constantF constantF referenceNameF v v r (referenceNameData m N)
    (constant_regular v) (constant_regular v) (constant_regular r) (reference_regular m N)
    (cross_refl _ _ (constant_regular v)) (cross_symm _ _ _ _ hr)
  have exactHeads := constant_binary_cross s u v r (inverse_grouping z R B m a d N h)
  exact cross_trans _ _ _ _ _ _ left (cross_trans _ _ _ _ _ _ exactHeads right)

theorem actual_Gauss_named_inverse_head_grouping_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      crossEquivalent (multiplyF shiftedNameF constantF) (multiplyF constantF referenceNameF)
        (multiplyData shiftedNameF constantF (shiftedNameData (var 0) (var 2) (var 3) (var 6))
          (headInverse oneCode one (cutoff (var 3) (var 6))))
        (multiplyData constantF referenceNameF (headInverse (scale (var 3) (var 0)) (var 2) (cutoff (var 3) (var 6)))
          (referenceNameData (var 3) (var 6)))) :=
  closeUniv 7 (.impI (named_head_grouping _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerNamedHeadGrouping
