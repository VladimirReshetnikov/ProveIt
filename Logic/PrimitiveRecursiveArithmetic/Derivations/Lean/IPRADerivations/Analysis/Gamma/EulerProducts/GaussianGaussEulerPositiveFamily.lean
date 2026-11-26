import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerFactorFamilies
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGaussEulerPositiveOffset
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamilyAlgebra

/-!
# The positive exponential product in the exact Gauss identity

Each actual full-head Euler exponential splits into the reference row
and a shared offset. Their indexed products retain the original
shifted and reference data used by the rational head products.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianGaussEulerPositiveFamily

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCompactCutoffSplit (point_data_congr)
open GaussianGammaEulerDenominatorGrouping (shiftedNumerator shiftedData)
open GaussianGammaEulerFullHeadInverse (negExpF negExpData negative_exponential_regular)
open GaussianGammaGaussEulerHeads (cutoff)
open GaussianGammaGaussReference (offset row_offset)
open GaussianGammaGaussReferenceProduct (argument)
open GaussianGaussEulerFactorFamilies
  (shiftedF referenceF shiftedExpBody referenceExpBody shiftedExpData referenceExpData
    shifted_exp_at reference_exp_at shifted_exp_regular reference_exp_regular)
open GaussianGaussEulerPositiveExponents (positive_from_original fixed_power_regular fixed_power_sum fixed_power_coeff_congr)
open GaussianGaussEulerPositiveOffset
  (offsetStageF offsetStageData offset_stage_regular offset_stage_cross offset_input
    repeatedOffsetF repeatedOffsetData repeated_offset_regular offset_and_unit)
open GaussianGaussEulerPowerRatio (fixedExponentF fixedPowerF fixedPowerData)
open GaussianGaussMultiplicationPowerRate (powerF row_power_input)
open GaussianGaussMultiplicationPowerPerturbation (rowData)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNamedFiniteProductFamily (rowF productData regularRows family_product_regular family_bounds family_regular)
open GaussianNamedFiniteProductFamilyAlgebra (multiplyBody body_at multiply_regular family_multiply_cross)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open GaussianRationalHorner (ofGaussian qadd positive_product)
open GaussianRationalSyntheticDivision (qadd_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def referenceOnShifted : PTm 2 := negExpData (argument (var 0)) (fstT (sndT (var 1))) (fstT (var 1))
def offsetBody : PTm 2 := offsetStageData (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1))))
  (fstT (sndT (var 1))) (fstT (var 1))

private theorem reference_on_shifted_at (r z B m N : PTm n) : Γ ⊢[PRAAx]
    inst2 referenceOnShifted r (shiftedData z B m N) ≐ negExpData (argument r) m N := by
  let x := shiftedData z B m N
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (negExpData (argument (var 0)) (var 1) (var 2) : PTm 3)
    (σ := ![r,fstT (sndT x),fstT x]) (σ' := ![r,m,N]) (fun i => by
      fin_cases i
      · exact .eqRefl _
      · exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      · exact fst_pair _ _)
  simpa only [referenceOnShifted,inst2,GaussianGammaEulerFullHeadInverse.subst_negExpData,
    GaussianGammaGaussReferenceProduct.subst_argument,subst_fstT,subst_sndT,Syn.subst_var,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons] using e

private theorem offset_at (r z B m N : PTm n) : Γ ⊢[PRAAx]
    inst2 offsetBody r (shiftedData z B m N) ≐ offsetStageData z B m N := by
  let x := shiftedData z B m N
  have pair := snd_pair (Γ := Γ) N (pairT m (pairT z B))
  have tail := (congrSnd pair).eqTrans (snd_pair _ _)
  have e := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (offsetStageData (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (sndT (sndT x)),sndT (sndT (sndT x)),fstT (sndT x),fstT x]) (σ' := ![z,B,m,N]) (fun i => by
      fin_cases i
      · exact (congrFst tail).eqTrans (fst_pair _ _)
      · exact (congrSnd tail).eqTrans (snd_pair _ _)
      · exact (congrFst pair).eqTrans (fst_pair _ _)
      · exact fst_pair _ _)
  simpa only [offsetBody,inst2,GaussianGaussEulerPositiveOffset.subst_offsetStageData,
    subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using e

private theorem exact_name_input (f : PR 2) (x y : PTm n) (h : Γ ⊢[PRAAx] pointCN f x)
    (eq : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] crossEquivalent f f x y := by
  apply GaussianNameConjugation.equal_samples_cross f f x y h (point_data_congr f x y eq h)
  refine .allI ?_
  have e : Γ.map Fm.shift ⊢[PRAAx] Syn.shift x ≐ Syn.shift y := by simpa [Fm.shift,Syn.shift] using eq.shift
  exact congrAp2 f (.eqRefl _) e

private theorem reference_on_shifted_regular (z B m N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] regularRows negExpF referenceOnShifted m (shiftedData z B m N) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have h : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
  simpa [Δ,sh,Syn.shift] using point_data_congr negExpF _ _
    (reference_on_shifted_at (Γ := Δ) (var 0) (sh z) (sh B) (sh m) (sh N)).eqSymm
    (negative_exponential_regular (argument (var 0)) (sh m) (sh N) h)

private theorem offset_row_regular (z B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] regularRows offsetStageF offsetBody m (shiftedData z B m N) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let Δ := lt (var 0) (sh m) :: Γ.map Fm.shift
  have hms : Δ ⊢[PRAAx] le one (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hm.shift.wk
  have hNs : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
  simpa [Δ,sh,Syn.shift] using point_data_congr offsetStageF _ _
    (offset_at (Γ := Δ) (var 0) (sh z) (sh B) (sh m) (sh N)).eqSymm
    (offset_stage_regular (sh z) (sh B) (sh m) (sh N) hms hNs)

private theorem row_split (r z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent negExpF (multiplyF negExpF offsetStageF)
      (negExpData (shiftedNumerator z B m r) (B*m) N)
      (multiplyData negExpF offsetStageF (negExpData (argument r) m N) (offsetStageData z B m N)) := by
  let w := shiftedNumerator z B m r
  let a := ofGaussian (argument r) m
  let b := offset z B m
  let c := ofGaussian w (B*m)
  let x := negExpData (argument r) m N
  let y := offsetStageData z B m N
  have sign := positive_from_original w (B*m) N hN
  have rf := positive_from_original (argument r) m N hN
  have stage := offset_stage_cross z B m N hm hN
  have prod := multiply_cross negExpF fixedPowerF offsetStageF fixedPowerF x (fixedPowerData a N) y (fixedPowerData b N)
    (negative_exponential_regular _ _ _ hN) (fixed_power_regular a N hN)
    (offset_stage_regular z B m N hm hN) (fixed_power_regular b N hN) rf stage
  have eq : Γ ⊢[PRAAx] qadd a b ≐ c :=
    (qadd_congr (.eqRefl _) (row_offset z B m r hB hm).eqSymm).eqTrans
      (GaussianRationalLinearProduct.add_sub_right a c (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ hB hm)))
  have combined := cross_trans _ _ _ _ _ _ prod
    (cross_trans _ _ _ _ _ _ (fixed_power_sum a b N hN) (fixed_power_coeff_congr _ _ N hN eq))
  exact cross_trans _ _ _ _ _ _ sign (cross_symm _ _ _ _ combined)

private theorem exact_rows_split (z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] equalRows negExpF (multiplyF negExpF offsetStageF) shiftedExpBody
      (multiplyBody negExpF offsetStageF referenceOnShifted offsetBody) m (shiftedData z B m N) (shiftedData z B m N) := by
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let r : PTm (n+1) := var 0
  let Δ := lt r (sh m) :: Γ.map Fm.shift
  let X := shiftedData (sh z) (sh B) (sh m) (sh N)
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hB.shift.wk
  have hm' : Δ ⊢[PRAAx] le one (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hm.shift.wk
  have hn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
  have l := shifted_exp_at (Γ := Δ) r (sh z) (sh B) (sh m) (sh N)
  have eq : Δ ⊢[PRAAx] inst2 (multiplyBody negExpF offsetStageF referenceOnShifted offsetBody) r X ≐
      multiplyData negExpF offsetStageF (negExpData (argument r) (sh m) (sh N)) (offsetStageData (sh z) (sh B) (sh m) (sh N)) := by
    rw [body_at]
    exact GaussianGammaEncodingRescaling.multiply_data_congr _ _ (reference_on_shifted_at _ _ _ _ _) (offset_at _ _ _ _ _)
  have left := exact_name_input negExpF _ _ (negative_exponential_regular _ _ _ hn) l.eqSymm
  have right := exact_name_input (multiplyF negExpF offsetStageF) _ _
    (multiply_fast _ _ _ _ (negative_exponential_regular (argument r) (sh m) (sh N) hn) (offset_stage_regular (sh z) (sh B) (sh m) (sh N) hm' hn))
    eq.eqSymm
  simpa [equalRows, Δ, sh, X, r, Syn.shift] using cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left)
    (cross_trans _ _ _ _ _ _ (row_split r (sh z) (sh B) (sh m) (sh N) hb hm' hn) right)

private theorem reference_family (z B m N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF negExpF referenceOnShifted)) referenceF
      (productData negExpF referenceOnShifted m (shiftedData z B m N)) (referenceExpData m N) := by
  apply family_product_cross _ _ _ _ _ _ _ (reference_on_shifted_regular z B m N hN) (reference_exp_regular m N hN)
  refine .allI (.impI ?_)
  let sh (a : PTm n) := Syn.shift a
  let r : PTm (n+1) := var 0
  let Δ := lt r (sh m) :: Γ.map Fm.shift
  have hn : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
  let X := negExpData (argument r) (sh m) (sh N)
  have l := reference_on_shifted_at (Γ := Δ) r (sh z) (sh B) (sh m) (sh N)
  have e := reference_exp_at (Γ := Δ) r (sh m) (sh N)
  have h := negative_exponential_regular (argument r) (sh m) (sh N) hn
  simpa [equalRows,Δ,sh,r,Syn.shift] using cross_trans negExpF negExpF negExpF _ X _
    (cross_symm _ _ _ _ (exact_name_input negExpF X _ h l.eqSymm))
    (exact_name_input negExpF X _ h e.eqSymm)

private theorem repeated_body_regular (f : PR 2) (m x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] regularRows f (var 1) m x := by
  refine .allI (.impI ?_)
  simpa [regularRows,inst2,Syn.shift,Fm.shift] using h.shift.wk (ψ := lt (var 0) (Syn.shift m))

private theorem repeated_body_radius (f : PR 2) (m x R : PTm n)
    (h : Γ ⊢[PRAAx] pointCN f x) (hb : Γ ⊢[PRAAx] GaussianNamedRepeatedProduct.bounds f R x) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF f (var 1)))
      (GaussianNamedFiniteProductName.nameF (GaussianNamedRepeatedProduct.repeatF f))
      (productData f (var 1) m x) (GaussianNamedFiniteProductName.data m R one x) := by
  let F := rowF f (var 1)
  let D := GaussianNamedFiniteProductName.rawData m x
  let S := GaussianNamedFiniteProductFamily.radius f (var 1) m x
  have hr := repeated_body_regular f m x h
  have hS := GaussianNamedFiniteProductName.raw_regular F m S one x (family_bounds f _ m x hr)
    (family_regular f _ m x hr)
  have hR := GaussianNamedFiniteProductName.raw_regular (GaussianNamedRepeatedProduct.repeatF f) m R one x
    (GaussianNamedRepeatedProduct.repeated_row_bounds f m R x hb) (GaussianNamedRepeatedProduct.repeated_row_regular f m x h)
  have same : Γ ⊢[PRAAx] GaussianValueNormalizerExtensionality.rawDiagonal (GaussianNamedFiniteProductName.rawF F)
      (GaussianNamedFiniteProductName.rawF F) D D zero := by
    refine .allI ?_
    simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,Syn.shift,ConciseIPRA.PTm.subst_zero] using
      GaussianRationalPowerDifference.distance_refl_zero (ap2 (GaussianNamedFiniteProductName.rawF F) (var 0) (Syn.shift D))
        (unit (var 0)) (unit_positive _)
  exact GaussianValueNormalizerExtensionality.normalized_names_equivalent _ _ _ _ _ _ zero hS hR same

private theorem offset_family (z B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] crossEquivalent (GaussianNamedFiniteProductName.nameF (rowF offsetStageF offsetBody)) repeatedOffsetF
      (productData offsetStageF offsetBody m (shiftedData z B m N)) (repeatedOffsetData z B m N) := by
  let x := offsetStageData z B m N
  have h := offset_stage_regular z B m N hm hN
  have eq : Γ ⊢[PRAAx] equalRows offsetStageF offsetStageF offsetBody (var 1) m (shiftedData z B m N) x := by
    refine .allI (.impI ?_)
    let sh (a : PTm n) := Syn.shift a
    let r : PTm (n+1) := var 0
    let Δ := lt r (sh m) :: Γ.map Fm.shift
    have hms : Δ ⊢[PRAAx] le one (sh m) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hm.shift.wk
    have hNs : Δ ⊢[PRAAx] le one (sh N) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hN.shift.wk
    have val := offset_at (Γ := Δ) r (sh z) (sh B) (sh m) (sh N)
    have rg := offset_stage_regular (sh z) (sh B) (sh m) (sh N) hms hNs
    simpa [equalRows,Δ,sh,r,x,Syn.shift,inst2] using
      cross_symm _ _ _ _ (exact_name_input offsetStageF _ _ rg val.eqSymm)
  have first := family_product_cross _ _ _ _ _ _ _ (offset_row_regular z B m N hm hN) (repeated_body_regular _ _ _ h) eq
  have bound := GaussianNamedRepeatedExponential.exponential_bounds fixedExponentF m _ _ (offset_input z B m N hN) hm
  exact cross_trans _ _ _ _ _ _ first (repeated_body_radius offsetStageF m x _ h bound)

theorem shifted_family_factorization (z B m N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hm : Γ ⊢[PRAAx] le one m) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    crossEquivalent shiftedF (multiplyF referenceF repeatedOffsetF) (shiftedExpData z B m N)
      (multiplyData referenceF repeatedOffsetF (referenceExpData m N) (repeatedOffsetData z B m N)) := by
  let X := shiftedData z B m N
  let F := GaussianNamedFiniteProductName.nameF (rowF negExpF referenceOnShifted)
  let G := GaussianNamedFiniteProductName.nameF (rowF offsetStageF offsetBody)
  let u := productData negExpF referenceOnShifted m X
  let v := productData offsetStageF offsetBody m X
  have hS := shifted_exp_regular z B m N hN
  have hF := reference_on_shifted_regular z B m N hN
  have hG := offset_row_regular z B m N hm hN
  have first := family_product_cross _ _ _ _ _ _ _ hS (multiply_regular _ _ _ _ _ _ hF hG)
    (exact_rows_split z B m N hB hm hN)
  have distributed := family_multiply_cross _ _ _ _ _ _ hF hG
  have last := multiply_cross F referenceF G repeatedOffsetF u (referenceExpData m N) v (repeatedOffsetData z B m N)
    (family_product_regular _ _ _ _ hF) (family_product_regular _ _ _ _ (reference_exp_regular m N hN))
    (family_product_regular _ _ _ _ hG) (repeated_offset_regular z B m N hm hN)
    (reference_family z B m N hN) (offset_family z B m N hm hN)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ distributed last)

theorem exponential_product (z R B m N : PTm n) (hm : Γ ⊢[PRAAx] le one m)
    (hN : Γ ⊢[PRAAx] le one N) (hB : Γ ⊢[PRAAx] le one B)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B)) : Γ ⊢[PRAAx]
    crossEquivalent (multiplyF shiftedF negExpF) (multiplyF (multiplyF powerF negExpF) referenceF)
      (multiplyData shiftedF negExpF (shiftedExpData z B m N) (negExpData oneCode one (cutoff m N)))
      (multiplyData (multiplyF powerF negExpF) referenceF
        (multiplyData powerF negExpF (rowData z R B m N) (negExpData (scale m z) B (cutoff m N))) (referenceExpData m N)) := by
  let E := negExpF
  let L := cutoff m N
  let s := shiftedExpData z B m N
  let r := referenceExpData m N
  let o := repeatedOffsetData z B m N
  let u := negExpData oneCode one L
  let v := negExpData (scale m z) B L
  let w := rowData z R B m N
  let p := multiplyData powerF E w v
  have hL := le_trans hN (GaussianGaussEulerCutoff.scaled_cutoff_later m N hm)
  have hS := family_product_regular _ _ _ _ (shifted_exp_regular z B m N hN)
  have hR := family_product_regular _ _ _ _ (reference_exp_regular m N hN)
  have hO := repeated_offset_regular z B m N hm hN
  have hU := negative_exponential_regular (Γ := Γ) oneCode one L hL
  have hV := negative_exponential_regular (Γ := Γ) (scale m z) B L hL
  have hW := GaussianRadiusExponentialName.name_regular _ _ _ (row_power_input z R B m N hm hN hB hz)
  have hP := multiply_fast powerF E w v hW hV
  have first := multiply_cross shiftedF (multiplyF referenceF repeatedOffsetF) E E s (multiplyData referenceF repeatedOffsetF r o) u u
    hS (multiply_fast _ _ _ _ hR hO) hU hU (shifted_family_factorization z B m N hB hm hN) (cross_refl _ _ hU)
  have assoc := GaussianNameRingLaws.multiply_associative referenceF repeatedOffsetF E r o u hR hO hU
  have transport := multiply_cross referenceF referenceF (multiplyF repeatedOffsetF E) (multiplyF powerF E)
    r r (multiplyData repeatedOffsetF E o u) p hR hR (multiply_fast _ _ _ _ hO hU) hP (cross_refl _ _ hR)
    (offset_and_unit z R B m N hm hN hB hz)
  exact cross_trans _ _ _ _ _ _ first (cross_trans _ _ _ _ _ _ assoc
    (cross_trans _ _ _ _ _ _ transport (GaussianNameRingLaws.multiply_commutative referenceF (multiplyF powerF E) r p hR hP)))

end LeanProofs.IPRA.Analysis.GaussianGaussEulerPositiveFamily
