import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.Reflection.GaussianGammaGaussReflectionFamily
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Multiplication.ReferenceProduct.GaussianGammaGaussReferencePrefix
import IPRADerivations.Analysis.RationalArithmetic.FiniteProducts.FactorOperations.GaussianRationalProductReverse

/-!
# The two Gamma factors of the reflection-family product

The complementary rows are the literal forward reference prefix. The
other rows give precisely the reverse of that same prefix, whose
finite product is unchanged by the checked reversal identity. Both
independently normalized families therefore name the original full
reference product.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionReferenceProducts

open_ipra
open GaussianCyclicSineProductSquare (data index)
open GaussianGammaGaussReflectionFamily (leftBody rightBody left_at right_ascending_at left_rows right_rows)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedFiniteProduct (sample body)
open GaussianNamedFiniteProductFamily (rowF row_at family_bounds family_regular productData radius regularRows)
open GaussianNamedFiniteProductName (rawF rawData raw_at raw_regular)
open GaussianRationalRectangularProduct (rowBody)
open GaussianRationalFiniteProduct (product_congr_bounded)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalProductReverse (reverseBody reverse_at reverse_product)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm)
open GaussianRationalPowerDifference (distance_refl_zero)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit_positive)
open GaussianValueNormalizerExtensionality (rawDiagonal normalized_names_equivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianGammaGaussReferenceProduct.rowF
local notation "B" => GaussianGammaGaussReferenceProduct.rowRadius

private def bodyFor (f : PR 3) : PTm 2 := rowBody (body f)

private theorem body_at (f : PR 3) (p i x : PTm n) :
    Γ ⊢[PRAAx] inst2 (bodyFor f) i (pairT p x) ≐ ap3 f p i x := by
  simpa [bodyFor,body,inst3] using GaussianRationalRectangularProduct.row_at (Γ := Γ) (body f) p i x

theorem forward_product (p N x : PTm n) :
    Γ ⊢[PRAAx] sample (rowF gammaF rightBody) p N (data N x) ≐ sample G p N (succ N) := by
  let t := bodyFor (rowF gammaF rightBody)
  let u := bodyFor G
  have hEq : Γ ⊢[PRAAx] termsEqual t u N (pairT p (data N x)) (pairT p (succ N)) := by
    refine .allI (.impI ?_)
    let P := Syn.shift p
    let K := Syn.shift N
    let y := Syn.shift x
    let i : PTm (n+1) := var 0
    let Δ := lt i K :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] lt i K := Prf.hyp0
    have a := (body_at (Γ := Δ) (rowF gammaF rightBody) P i (data K y)).eqTrans (row_at gammaF rightBody P i (data K y))
    have b := (body_at (Γ := Δ) G P i (succ K)).eqTrans (GaussianGammaGaussReferenceProduct.row_at P i (succ K))
    have read := a.eqTrans (congrAp2 gammaF (.eqRefl _) (right_ascending_at K y i hi))
    simpa [termsEqual,Δ,P,K,y,i,Syn.shift] using read.eqTrans b.eqSymm
  exact product_congr_bounded t u N _ _ hEq

theorem reversed_product (p N x : PTm n) :
    Γ ⊢[PRAAx] sample (rowF gammaF leftBody) p N (data N x) ≐ sample G p N (succ N) := by
  let t := bodyFor (rowF gammaF leftBody)
  let u := bodyFor G
  have hEq : Γ ⊢[PRAAx] termsEqual t (reverseBody u) N (pairT p (data N x)) (pairT N (pairT p (succ N))) := by
    refine .allI (.impI ?_)
    let P := Syn.shift p
    let K := Syn.shift N
    let y := Syn.shift x
    let i : PTm (n+1) := var 0
    let Δ := lt i K :: Γ.map Fm.shift
    have a := (body_at (Γ := Δ) (rowF gammaF leftBody) P i (data K y)).eqTrans (row_at gammaF leftBody P i (data K y))
    have b := (reverse_at (Γ := Δ) u K (pairT P (succ K)) i).eqTrans
      ((body_at G P (index K i) (succ K)).eqTrans (GaussianGammaGaussReferenceProduct.row_at P (index K i) (succ K)))
    have read := a.eqTrans (congrAp2 gammaF (.eqRefl _) (left_at K y i))
    simpa [termsEqual,Δ,P,K,y,i,Syn.shift] using read.eqTrans b.eqSymm
  exact (product_congr_bounded t (reverseBody u) N _ _ hEq).eqTrans (reverse_product u N _)

private theorem family_reference_cross (t : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows gammaF t N (data N x))
    (readback : ∀ {l : ℕ} {Δ : List (Fm PTm l)} (p N x : PTm l),
      Δ ⊢[PRAAx] sample (rowF gammaF t) p N (data N x) ≐ sample G p N (succ N)) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF gammaF t)) GaussianGammaGaussReferenceProduct.nameF
      (productData gammaF t N (data N x)) (GaussianGammaGaussReferenceProduct.data (succ N)) := by
  let f := rowF gammaF t
  let R := radius gammaF t N (data N x)
  let X := data N x
  let m := succ N
  have regular := raw_regular f N R one X (family_bounds _ _ _ _ h) (family_regular _ _ _ _ h)
  have prefReg := raw_regular G N (B m) one m (GaussianGammaGaussReferencePrefix.prefix_bounds (Γ := Γ) N)
    (GaussianGammaGaussReferencePrefix.prefix_regular N)
  have hDiag : Γ ⊢[PRAAx] rawDiagonal (rawF f) (rawF G) (rawData N X) (rawData N m) zero := by
    refine .allI ?_
    let K := Syn.shift N
    let y := Syn.shift x
    let p : PTm (n+1) := var 0
    let Δ := Γ.map Fm.shift
    have e : Δ ⊢[PRAAx] ap2 (rawF f) p (rawData K (data K y)) ≐ ap2 (rawF G) p (rawData K (succ K)) :=
      (raw_at f p K (data K y)).eqTrans ((readback p K y).eqTrans (raw_at G p K (succ K)).eqSymm)
    simpa [rawDiagonal,X,m,K,y,p,Δ,Syn.shift] using
      distance_congr e.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
        (distance_refl_zero (ap2 (rawF G) p (rawData K (succ K))) _ (unit_positive p))
  have pref := normalized_names_equivalent _ _ _ _ _ _ _ regular prefReg hDiag
  exact cross_trans _ _ _ _ _ _ pref
    (cross_symm _ _ _ _ (GaussianGammaGaussReferencePrefix.full_prefix_cross N))

theorem left_reference_product (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF gammaF leftBody)) GaussianGammaGaussReferenceProduct.nameF
      (productData gammaF leftBody N (data N x)) (GaussianGammaGaussReferenceProduct.data (succ N)) :=
  family_reference_cross leftBody N x (left_rows N x) (fun p n x => reversed_product p n x)

theorem right_reference_product (N x : PTm n) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF gammaF rightBody)) GaussianGammaGaussReferenceProduct.nameF
      (productData gammaF rightBody N (data N x)) (GaussianGammaGaussReferenceProduct.data (succ N)) :=
  family_reference_cross rightBody N x (right_rows N x) (fun p n x => forward_product p n x)

theorem actual_Gauss_reflection_reference_family_products_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF gammaF leftBody)) GaussianGammaGaussReferenceProduct.nameF
        (productData gammaF leftBody (var 1) (data (var 1) (var 0)))
        (GaussianGammaGaussReferenceProduct.data (succ (var 1))) ⋏
      crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF gammaF rightBody)) GaussianGammaGaussReferenceProduct.nameF
        (productData gammaF rightBody (var 1) (data (var 1) (var 0)))
        (GaussianGammaGaussReferenceProduct.data (succ (var 1)))) :=
  closeUniv 2 (.andI (left_reference_product _ _) (right_reference_product _ _))

end LeanProofs.IPRA.Analysis.GaussianGammaGaussReflectionReferenceProducts
