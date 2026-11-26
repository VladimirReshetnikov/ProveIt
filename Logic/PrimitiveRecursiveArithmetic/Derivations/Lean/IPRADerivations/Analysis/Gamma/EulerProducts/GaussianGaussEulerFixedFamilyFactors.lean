import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerNamedHeadGrouping
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerFactorFamilies
import IPRADerivations.Analysis.Gamma.FunctionalEquations.GaussianGaussMultiplicationFixedProducts
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamilyAlgebra

/-!
# The fixed Gauss Euler products factor into the literal heads and exponentials

The normalized shifted and reference products use their original row
programs. The observation at successor precision compares with the
full-head factorization at the requested precision. The same finite
fold consequently splits into the inverse-head and exponential families.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerFixedFamilyFactors

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator shiftedData)
open GaussianGammaEulerFullHeadInverse (nameF negExpF data original_factorization)
open GaussianGammaEulerReciprocalInverse (eulerF eulerData)
open GaussianGammaGaussReferenceProduct (argument)
open GaussianGammaGaussShiftedProduct (source)
open GaussianGaussEulerNamedHeadGrouping (shiftedNameF shiftedNameData referenceNameF referenceNameData)
open GaussianGaussEulerFactorFamilies (shiftedExpBody referenceExpBody shiftedExpData referenceExpData shifted_exp_at
  reference_exp_at shifted_exp_regular reference_exp_regular)
open GaussianGaussEulerInverseHeadGrouping (shiftedInverseBody referenceInverseBody shifted_inverse_at reference_inverse_at)
open GaussianNamedConstantFamilyProduct (constant_rows_regular)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_trans)
open GaussianNamedFiniteProduct (rowDistance)
open GaussianNamedFiniteProductFamily (rowF row_at radius family_bounds family_regular)
open GaussianNamedFiniteProductFamilyAlgebra (multiplyBody body_at multiply_regular family_multiply_cross)
open GaussianNamedFiniteProductFamilyCongruence (row_bounds_widen)
open GaussianNamedFiniteProductName (cofinalRows cofinal_raw rowBounds rowRegular raw_regular)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "referenceRows" => GaussianGammaGaussReferenceEulerProduct.rowF
local notation "referenceRowData" => GaussianGammaGaussReferenceEulerProduct.rowData
local notation "referenceRowRadius" => GaussianGammaGaussReferenceEulerProduct.rowRadius
local notation "referenceThreshold" => GaussianGammaGaussReferenceEulerProduct.threshold
local notation "shiftedRows" => GaussianGammaGaussEulerProduct.rowF
local notation "shiftedRowData" => GaussianGammaGaussEulerProduct.rowData
local notation "shiftedRowRadius" => GaussianGammaGaussEulerProduct.rowRadius
local notation "shiftedThreshold" => GaussianGammaGaussEulerProduct.threshold
local notation "fixedShiftedF" => GaussianGaussMultiplicationFixedProducts.shiftedF
local notation "fixedReferenceF" => GaussianGaussMultiplicationFixedProducts.referenceF
local notation "fixedShiftedData" => GaussianGaussMultiplicationFixedProducts.shiftedData
local notation "fixedReferenceData" => GaussianGaussMultiplicationFixedProducts.referenceData
local notation "shiftedExpF" => GaussianGaussEulerFactorFamilies.shiftedF
local notation "referenceExpF" => GaussianGaussEulerFactorFamilies.referenceF
local notation "nf" => GaussianNamedFiniteProductName.nameF
local notation "nd" => GaussianNamedFiniteProductName.data

private abbrev shiftedFactorBody : PTm 2 := multiplyBody constantF negExpF shiftedInverseBody shiftedExpBody
private abbrev referenceFactorBody : PTm 2 := multiplyBody constantF negExpF referenceInverseBody referenceExpBody

private theorem normalized_product_cross (f g : PR 3) (N R S L M C x y : PTm n)
    (bf : Γ ⊢[PRAAx] rowBounds f N R x) (bg : Γ ⊢[PRAAx] rowBounds g N S y)
    (rf : Γ ⊢[PRAAx] rowRegular f N L x) (rg : Γ ⊢[PRAAx] rowRegular g N M y)
    (he : Γ ⊢[PRAAx] cofinalRows f g N C x y) :
    Γ ⊢[PRAAx] crossEquivalent (nf f) (nf g) (nd N R L x) (nd N S M y) := by
  have rate := cofinal_raw f g N (R+S) C x y
    (row_bounds_widen f N R (R+S) x bf (le_add_right R S))
    (row_bounds_widen g N S (R+S) y bg (le_add_left S R)) he
  exact GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ _
    (raw_regular f N R L x bf rf) (raw_regular g N S M y bg rg) rate

private theorem factor_sample (p z R B a d N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerReciprocalInverse.source z R B a d N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 eulerF (succ p) (eulerData z R B d N))
      (ap2 nameF p (data z B N)) two (unit p) := by
  let U := unit p
  let V := unit (succ p)
  have hp : Γ ⊢[PRAAx] le one U := unit_positive p
  have hv : Γ ⊢[PRAAx] le one V := unit_positive (succ p)
  have grow : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_succ_self p)
  have wide : Γ ⊢[PRAAx] le ((V+U)*U) (two*(V*U)) := by
    ipra_le 𝔞 U*sl grow
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hv hp) hp wide
    (cross_at _ _ _ _ (succ p) p (original_factorization z R B a d N h))

private theorem factor_data_congr {v v' e e' : PTm n} (hv : Γ ⊢[PRAAx] v ≐ v') (he : Γ ⊢[PRAAx] e ≐ e') :
    Γ ⊢[PRAAx] multiplyData constantF negExpF v e ≐ multiplyData constantF negExpF v' e' := by
  simpa only [GaussianNameArithmetic.subst_multiplyData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (multiplyData constantF negExpF (var 0) (var 1) : PTm 2)
      (σ := ![v,e]) (σ' := ![v',e']) (fun i => by fin_cases i; exact hv; exact he)

private theorem shifted_row_comparison (s z R B m a d N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hn : Γ ⊢[PRAAx] le (shiftedThreshold s R m a d) N) :
    Γ ⊢[PRAAx] cofinalRows shiftedRows (rowF nameF shiftedFactorBody) m two (shiftedRowData z R B m d N)
      (shiftedData z B m N) := by
  refine .allI (.allI (.impI ?_))
  let sh (w : PTm n) := Syn.shift (Syn.shift w)
  let Δ := lt (var 0) (sh m) :: (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let i : PTm (n+2) := var 0
  let w := shiftedNumerator (sh z) (sh B) (sh m) i
  have hs' : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh m) (sh a) (sh d) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift.shift.wk
  have hn' : Δ ⊢[PRAAx] le (shiftedThreshold (sh s) (sh R) (sh m) (sh a) (sh d)) (sh N) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hn.shift.shift.wk
  have hrow := GaussianGammaGaussShiftedProduct.row_source (sh z) (sh R) (sh B) (sh m) i (sh a) (sh d) hs'
    (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh m))
  have eu := GaussianGaussEulerCutoffUniform.cutoff_source (sh s) w (sh R+one) (sh B*sh m) (sh a) (sh d*sh m)
    (sh N) hrow hn'
  let X := shiftedData (sh z) (sh B) (sh m) (sh N)
  have er : Δ ⊢[PRAAx] ap3 (rowF nameF shiftedFactorBody) p i X ≐ ap2 nameF p (data w (sh B*sh m) (sh N)) := by
    refine (row_at nameF shiftedFactorBody p i X).eqTrans (congrAp2 nameF (.eqRefl _) ?_)
    rw [body_at]
    exact factor_data_congr (shifted_inverse_at i (sh z) (sh B) (sh m) (sh N))
      (shifted_exp_at i (sh z) (sh B) (sh m) (sh N))
  have el := GaussianGammaGaussEulerProduct.row_at (Γ := Δ) p i (sh z) (sh R) (sh B) (sh m) (sh d) (sh N)
  have result := distance_congr el.eqSymm er.eqSymm (.eqRefl _) (.eqRefl _)
    (factor_sample p w (sh R+one) (sh B*sh m) (sh a) (sh d*sh m) (sh N) (.andI hrow eu.andE₂.andE₁))
  simpa [cofinalRows,rowDistance,Δ,sh,p,i,X,Syn.shift,two,one] using result

private theorem reference_row_comparison (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (referenceThreshold s m) N) :
    Γ ⊢[PRAAx] cofinalRows referenceRows (rowF nameF referenceFactorBody) m two (referenceRowData m N) (pairT m N) := by
  refine .allI (.allI (.impI ?_))
  let sh (w : PTm n) := Syn.shift (Syn.shift w)
  let Δ := lt (var 0) (sh m) :: (Γ.map Fm.shift).map Fm.shift
  let p : PTm (n+2) := var 1
  let i : PTm (n+2) := var 0
  have hn' : Δ ⊢[PRAAx] le (referenceThreshold (sh s) (sh m)) (sh N) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hn.shift.shift.wk
  have hrow := GaussianGammaGaussReferenceProduct.row_source i (sh m) (Prf.hyp0 : Δ ⊢[PRAAx] lt i (sh m))
  have eu := GaussianGaussEulerCutoffUniform.cutoff_source (sh s) (argument i) one (sh m) one (sh m)
    (sh N) hrow hn'
  let X := pairT (sh m) (sh N)
  have er : Δ ⊢[PRAAx] ap3 (rowF nameF referenceFactorBody) p i X ≐ ap2 nameF p (data (argument i) (sh m) (sh N)) := by
    refine (row_at nameF referenceFactorBody p i X).eqTrans (congrAp2 nameF (.eqRefl _) ?_)
    rw [body_at]
    exact factor_data_congr (reference_inverse_at i (sh m) (sh N)) (reference_exp_at i (sh m) (sh N))
  have el := GaussianGammaGaussReferenceEulerProduct.row_at (Γ := Δ) p i (sh m) (sh N)
  have result := distance_congr el.eqSymm er.eqSymm (.eqRefl _) (.eqRefl _)
    (factor_sample p (argument i) one (sh m) one (sh m) (sh N) (.andI hrow eu.andE₂.andE₁))
  simpa [cofinalRows,rowDistance,Δ,sh,p,i,X,Syn.shift,two,one] using result

private theorem threshold_positive (s R a d N : PTm n) (hn : Γ ⊢[PRAAx]
    le (GaussianGammaEulerInverseApproximationName.cutoff s R a d) N) : Γ ⊢[PRAAx] le one N := by
  refine le_trans ?_ hn
  unfold GaussianGammaEulerInverseApproximationName.cutoff
  exact le_trans (zero_lt_succ _) (le_add_left _ _)

theorem shifted_factorization (s z R B m a d N : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B m a d) (hn : Γ ⊢[PRAAx] le (shiftedThreshold s R m a d) N) :
    Γ ⊢[PRAAx] crossEquivalent fixedShiftedF (multiplyF shiftedNameF shiftedExpF)
      (fixedShiftedData z R B m d N)
      (multiplyData shiftedNameF shiftedExpF (shiftedNameData z B m N) (shiftedExpData z B m N)) := by
  let X := shiftedData z B m N
  let t := shiftedFactorBody
  have hN := threshold_positive s (R+one) a (d*m) N hn
  have hc := constant_rows_regular (Γ := Γ) shiftedInverseBody m X
  have he := shifted_exp_regular z B m N hN
  have hf := multiply_regular constantF negExpF shiftedInverseBody shiftedExpBody m X hc he
  have first := normalized_product_cross shiftedRows (rowF nameF t) m (shiftedRowRadius R m d) (radius nameF t m X)
    one one two (shiftedRowData z R B m d N) X (GaussianGaussMultiplicationFixedProducts.shifted_row_bounds s z R B m a d N hs hn)
    (family_bounds _ _ _ _ hf) (GaussianGaussMultiplicationFixedProducts.shifted_row_regular s z R B m a d N hs hn)
    (family_regular _ _ _ _ hf) (shifted_row_comparison s z R B m a d N hs hn)
  exact cross_trans _ _ _ _ _ _ first (family_multiply_cross constantF negExpF shiftedInverseBody shiftedExpBody m X hc he)

theorem reference_factorization (s m N : PTm n) (hn : Γ ⊢[PRAAx] le (referenceThreshold s m) N) :
    Γ ⊢[PRAAx] crossEquivalent fixedReferenceF (multiplyF referenceNameF referenceExpF) (fixedReferenceData m N)
      (multiplyData referenceNameF referenceExpF (referenceNameData m N) (referenceExpData m N)) := by
  let X := pairT m N
  let t := referenceFactorBody
  have hN := threshold_positive s one one m N hn
  have hc := constant_rows_regular (Γ := Γ) referenceInverseBody m X
  have he := reference_exp_regular m N hN
  have hf := multiply_regular constantF negExpF referenceInverseBody referenceExpBody m X hc he
  have first := normalized_product_cross referenceRows (rowF nameF t) m (referenceRowRadius m) (radius nameF t m X)
    one one two (referenceRowData m N) X (GaussianGaussMultiplicationFixedProducts.reference_row_bounds s m N hn)
    (family_bounds _ _ _ _ hf) (GaussianGaussMultiplicationFixedProducts.reference_row_regular s m N hn)
    (family_regular _ _ _ _ hf) (reference_row_comparison s m N hn)
  exact cross_trans _ _ _ _ _ _ first (family_multiply_cross constantF negExpF referenceInverseBody referenceExpBody m X hc he)

theorem actual_Gauss_shifted_Euler_product_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶
      le (shiftedThreshold (var 0) (var 2) (var 4) (var 5) (var 6)) (var 7) ⟶
      crossEquivalent fixedShiftedF (multiplyF shiftedNameF shiftedExpF)
        (fixedShiftedData (var 1) (var 2) (var 3) (var 4) (var 6) (var 7))
        (multiplyData shiftedNameF shiftedExpF (shiftedNameData (var 1) (var 3) (var 4) (var 7))
          (shiftedExpData (var 1) (var 3) (var 4) (var 7)))) :=
  closeUniv 8 (.impI (.impI (shifted_factorization _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_Gauss_reference_Euler_product_factorization_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (referenceThreshold (var 0) (var 1)) (var 2) ⟶
      crossEquivalent fixedReferenceF (multiplyF referenceNameF referenceExpF) (fixedReferenceData (var 1) (var 2))
        (multiplyData referenceNameF referenceExpF (referenceNameData (var 1) (var 2)) (referenceExpData (var 1) (var 2)))) :=
  closeUniv 3 (.impI (reference_factorization _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerFixedFamilyFactors
