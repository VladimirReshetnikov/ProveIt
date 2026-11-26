import IPRADerivations.Analysis.Gamma.BohrMollerup.Uniqueness.GaussianBohrMollerupDifferenceTransform
import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalWendelBoundary

/-!
# Zero and cancellation for actual regular name differences
-/

set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace LeanProofs.IPRA.Analysis.GaussianBohrMollerupZeroAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaEulerRationalLogOrder (add_order order_refl)
open GaussianGammaRationalWendelBoundary (zero_product_at)
open GaussianNameArithmetic (addF addData add_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (zeroF zero_at zero_fast negativeF negativeData negative_fast
  add_associative add_commutative add_negative add_zero add_zero_left)
open GaussianNamedDifference (nameF data name_regular)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (qzero)
open GaussianRationalMetric (qsub)
open GaussianRationalSyntheticDivision (qsub_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem negative_zero (x : PTm n) : Γ ⊢[PRAAx] crossEquivalent (negativeF zeroF) zeroF (negativeData x) x := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _ (negative_fast _ _ (zero_fast x)) (zero_fast x)
  refine .allI ?_
  let X := Syn.shift x
  let p : PTm (n+1) := var 0
  let Δ := Γ.map Fm.shift
  have start := GaussianNameRingLaws.negative_at (Γ := Δ) zeroF X p
  have read := (qsub_congr (.eqRefl _) (zero_at (Γ := Δ) (GaussianFastValueCut.exponent (one+one) p) X)).eqTrans
    (GaussianCoefficientNormOrder.qsub_self (qzero : PTm (n+1)))
  have raw := (GaussianNameArithmetic.recode_congr read).eqTrans
    (GaussianExponentialReference.recode_fixed _ GaussianRationalSyntheticDivision.qzero_canonical)
  simpa [Syn.shift,Δ,X,p] using start.eqTrans (raw.eqTrans (zero_at p X).eqSymm)

theorem subtract_zero (F : PR 2) (x y : PTm n) (hf : Γ ⊢[PRAAx] pointCN F x) :
    Γ ⊢[PRAAx] crossEquivalent (nameF F zeroF) F (data x y) x := by
  have a := cross_trans _ _ _ _ _ _ (negative_zero (Γ := Γ) y)
    (GaussianGammaRationalWendelBoundary.zero_data_cross y x)
  have b := add_cross F F (negativeF zeroF) zeroF x x (negativeData y) x hf hf
    (negative_fast _ _ (zero_fast y)) (zero_fast _) (cross_refl _ _ hf) a
  exact cross_trans _ _ _ _ _ _ b (GaussianNameRingLaws.add_zero F x hf)

theorem subtract_add (F G : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx]
    crossEquivalent (addF (nameF F G) G) F (addData (data x y) y) x := by
  let N := negativeF G
  let z := negativeData y
  have hz := negative_fast G y hg
  have a := add_associative F N G x z y hf hz hg
  have b := cross_trans _ _ _ _ _ _ (add_commutative N G z y hz hg)
    (cross_trans _ _ _ _ _ _ (add_negative G y hg)
      (GaussianGammaRationalWendelBoundary.zero_data_cross y x))
  have c := add_cross F F (addF N G) zeroF x x (addData z y) x hf hf
    (add_fast _ _ _ _ hz hg) (zero_fast _) (cross_refl _ _ hf) b
  exact cross_trans _ _ _ _ _ _ a (cross_trans _ _ _ _ _ _ c (GaussianNameRingLaws.add_zero F x hf))

theorem order_of_difference_nonpositive (F G : PR 2) (x y : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (ord : Γ ⊢[PRAAx] realOrder (nameF F G) zeroF (data x y) y) : Γ ⊢[PRAAx] realOrder F G x y :=
  GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ (subtract_add F G x y hf hg)) (add_zero_left G y hg)
    (add_order _ _ G G _ y y y ord (order_refl _ _ hg))

theorem scaled_zero (b y : PTm n) : Γ ⊢[PRAAx]
    crossEquivalent (productF zeroF) zeroF (productData zeroF b y) y := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianNamedNaturalScaleOrder.regular _ _ _ (zero_fast y)) (zero_fast y)
  refine .allI ?_
  let Y := Syn.shift y
  let B := Syn.shift b
  let p : PTm (n+1) := var 0
  have read := GaussianNaturalScaleProductName.product_at (Γ := Γ.map Fm.shift) zeroF p B Y
  have folded := GaussianRationalNaturalScale.natScale_congr (.eqRefl B)
    (zero_at (Γ := Γ.map Fm.shift) (GaussianNaturalScaleProductName.clock zeroF p B Y) Y)
  have zeroScale := (GaussianRationalNaturalScale.natScale_as_product (Γ := Γ.map Fm.shift) B qzero).eqTrans
    (GaussianRationalSyntheticDivision.qmul_zero_right _)
  have result := read.eqTrans (folded.eqTrans (zeroScale.eqTrans (zero_at p Y).eqSymm))
  simpa [Syn.shift,p,Y,B,GaussianNaturalScaleProductName.sample] using result

end LeanProofs.IPRA.Analysis.GaussianBohrMollerupZeroAlgebra
