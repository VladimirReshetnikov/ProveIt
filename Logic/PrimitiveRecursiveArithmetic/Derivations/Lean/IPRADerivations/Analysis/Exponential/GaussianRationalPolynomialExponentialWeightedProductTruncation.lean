import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialFixedRadius
import IPRADerivations.Analysis.Exponential.GaussianRationalPolynomialExponentialProductTruncation
import IPRADerivations.Core.CommonLemmas

/-!
# Weighted truncation of the original exponential recomposition product

The stored exponential prefix has weighted coefficient mass at most 3^L
when the original exponent has weighted mass at most L. Dilation and the
original convolution then control the discarded product terms. The original
stored product and the original recomposition value are retained when the
query is normalized at any positive rational radius.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialWeightedProductTruncation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientL1 (coefficientNorm)
open GaussianDominantPairAlgebra (radiusPoint)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (canonical evaluate positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalMonicReduction (evaluate_congr)
open GaussianRationalPolynomialDilation (dilated weightedNorm dilated_length dilated_canonical dilation_evaluation)
open GaussianRationalPolynomialExponentialFixedRadius (normalized_bound normalized_roundtrip)
open GaussianRationalPolynomialExponentialProductTruncation (exponentialPrefix exponential_prefix_length
  exponential_prefix_evaluation polynomial polynomial_length)
open GaussianRationalPolynomialExponentialRecomposition (value subst_value)
open GaussianRationalPolynomialProduct (product product_length product_evaluation)
open GaussianRationalSyntheticBounds (natCode natCode_nonnegative natCode_multiply)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalTravelScaling (ratio)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr subst_length)
open RationalArgmin (rationalLE rationalLE_congr)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem weighted_exponential_prefix_mass (C N K m t L : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hm : Γ ⊢[PRAAx] le m (K*N)) (hL : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode L)) :
    Γ ⊢[PRAAx] rationalLE (weightedNorm (exponentialPrefix C N K m) m t) (natCode (pw (num 3) L)) := by
  let P := exponentialPrefix C N K m
  let Q := exponentialPrefix (dilated C N t) N K m
  have hCShift : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by
    simpa only [Fm.shift,Fm.subst_eq,subst_length,ConciseIPRA.PTm.subst_succ,Syn.shift] using hC.shift
  have hmShift : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift m) (Syn.shift K*Syn.shift N) := by
    simpa only [Fm.shift,subst_le,LeanProofs.IPRA.PTm.subst_mul,Syn.shift] using hm.shift
  have mass : Γ ⊢[PRAAx] coefficientNorm (dilated P m t) ≐ coefficientNorm Q := by
    refine GaussianPolynomialNormBuffers.norm_entries (dilated P m t) Q (succ m) (dilated_length P m t)
      (exponential_prefix_length (dilated C N t) N K m) (.allI (.impI ?_))
    let Δ := lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift
    let e := monus (Syn.shift m) (var 0)
    have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift m) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    have complement : Δ ⊢[PRAAx] monus (Syn.shift m) e ≐ var 0 := Common.monus_monus_of_le hi
    have coeff := GaussianRationalPolynomialExponentialDilation.prefix_coefficient (Γ := Δ) (Syn.shift C) (Syn.shift N)
      (Syn.shift K) (Syn.shift m) (Syn.shift t) e hCShift.wk hmShift.wk (Common.monus_le_self _ _)
    simpa only [P,Q,Δ,Syn.shift,exponentialPrefix,GaussianPolynomialLowPrefix.subst_polynomial,
      GaussianRationalPolynomialExponential.subst_polynomial,GaussianRationalPolynomialDilation.subst_dilated,
      ConciseIPRA.PTm.subst_succ,LeanProofs.IPRA.PTm.subst_mul] using
      (entry_congr (.eqRefl _) complement.eqSymm).eqTrans (coeff.eqSymm.eqTrans (entry_congr (.eqRefl _) complement))
  exact rationalLE_congr mass.eqSymm (.eqRefl _)
    (GaussianRationalPolynomialExponentialProductTruncation.exponential_prefix_mass (dilated C N t) N K m L
      (dilated_length C N t) (dilated_canonical C N t) hm hL)

theorem normalized_polynomial_evaluation (P C r N m t z : PTm n) : Γ ⊢[PRAAx]
    evaluate (dilated (polynomial P C r N m) m t) z ≐ evaluate (polynomial P C r N m) (qmul t z) :=
  dilation_evaluation (polynomial P C r N m) m t z (polynomial_length P C r N m)

theorem normalized_tail (P C r N m t z H B A L : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ r) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] le m (m*N))
    (hB : Γ ⊢[PRAAx] le one B) (hHB : Γ ⊢[PRAAx] le H B) (hz : Γ ⊢[PRAAx] bounded z H B)
    (hA : Γ ⊢[PRAAx] rationalLE (weightedNorm P r t) (natCode A))
    (hL : Γ ⊢[PRAAx] rationalLE (weightedNorm C N t) (natCode L)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (evaluate P (qmul t z)) (value C N m (qmul t z)))
      (evaluate (polynomial P C r N m) (qmul t z)) ((A*pw (num 3) L)*pw H (succ m)) (pw B (succ m)) := by
  let Q := exponentialPrefix C N m m
  let F := product P Q r m
  let U := pw (num 3) L
  let w := qmul t z
  have hQ : Γ ⊢[PRAAx] length Q ≐ succ m := exponential_prefix_length C N m m
  have hOut : Γ ⊢[PRAAx] le m (r+m) := le_add_left m r
  have e := GaussianFiniteExponentialWeightedNorm.multiply_bounds (weightedNorm P r t) (weightedNorm Q m t)
    (natCode A) (natCode U) (GaussianFiniteExponentialWeightedNorm.weighted_nonnegative Q m t)
    (natCode_nonnegative A) hA (weighted_exponential_prefix_mass C N m m t L hC hm hL)
  have mass : Γ ⊢[PRAAx] rationalLE (weightedNorm F (r+m) t) (natCode (A*U)) :=
    RationalArgmin.transitive (GaussianRationalPolynomialDilation.weighted_product_bound P Q r m t hP hQ)
      (rationalLE_congr (.eqRefl _) (natCode_multiply A U) e)
  have tail := GaussianShrinkingPolynomialTail.weighted_coefficient_tail F (r+m) m t z (A*U) one H B
    (product_length P Q r m) hOut (le_refl one) hB hHB mass hz
  have full := (product_evaluation P Q r m w hP hQ).eqTrans
    (qmul_congr (.eqRefl _) (exponential_prefix_evaluation C N m w hm))
  exact distance_congr full (GaussianPolynomialLowPrefix.original_evaluation F (r+m) m w hOut).eqSymm
    (.eqRefl _) (one_mul _) tail

private theorem value_congr (C N m u w : PTm n) (he : Γ ⊢[PRAAx] u ≐ w) : Γ ⊢[PRAAx]
    value C N m u ≐ value C N m w := by
  simpa only [subst_value,Syn.subst_var,Matrix.cons_val] using
    Prf.eqCongr (value (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![C,N,m,u]) (σ' := ![C,N,m,w])
      (fun i => by fin_cases i; exact .eqRefl _; exact .eqRefl _; exact .eqRefl _; exact he)

theorem fixed_radius_tail (P C r N m w U D H B A L : PTm n)
    (hP : Γ ⊢[PRAAx] length P ≐ succ r) (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hm : Γ ⊢[PRAAx] le m (m*N))
    (hU : Γ ⊢[PRAAx] le one U) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B)
    (hHB : Γ ⊢[PRAAx] le (D*H) (U*B)) (hCan : Γ ⊢[PRAAx] canonical w) (hw : Γ ⊢[PRAAx] bounded w H B)
    (hA : Γ ⊢[PRAAx] rationalLE (weightedNorm P r (radiusPoint U D)) (natCode A))
    (hL : Γ ⊢[PRAAx] rationalLE (weightedNorm C N (radiusPoint U D)) (natCode L)) : Γ ⊢[PRAAx]
    distanceBounded (qmul (evaluate P w) (value C N m w)) (evaluate (polynomial P C r N m) w)
      ((A*pw (num 3) L)*pw (D*H) (succ m)) (pw (U*B) (succ m)) := by
  let z := ratio U D w
  let u := qmul (radiusPoint U D) z
  have he : Γ ⊢[PRAAx] u ≐ w := normalized_roundtrip w U D hU hD hCan
  have tail := normalized_tail P C r N m (radiusPoint U D) z (D*H) (U*B) A L hP hC hm
    (positive_product U B hU hB) hHB (normalized_bound w U D H B hU hB hw) hA hL
  exact distance_congr (qmul_congr (evaluate_congr (.eqRefl P) he) (value_congr C N m u w he))
    (evaluate_congr (.eqRefl (polynomial P C r N m)) he) (.eqRefl _) (.eqRefl _) tail

theorem actual_fixed_radius_weighted_product_tail_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (let P := var 0
     let C := var 1
     let r := var 2
     let N := var 3
     let m := var 4
     let w := var 5
     let U := var 6
     let D := var 7
     let H := var 8
     let B := var 9
     let A := var 10
     let L := var 11
     ((length P ≐ succ r) ⋏ ((length C ≐ succ N) ⋏ (le m (m*N) ⋏ (le one U ⋏ (le one D ⋏ (le one B ⋏
       (le (D*H) (U*B) ⋏ (canonical w ⋏ (bounded w H B ⋏ (rationalLE (weightedNorm P r (radiusPoint U D)) (natCode A) ⋏
       rationalLE (weightedNorm C N (radiusPoint U D)) (natCode L))))))))))) ⟶
       distanceBounded (qmul (evaluate P w) (value C N m w)) (evaluate (polynomial P C r N m) w)
         ((A*pw (num 3) L)*pw (D*H) (succ m)) (pw (U*B) (succ m))) :=
  closeUniv 12 (.impI (fixed_radius_tail (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRationalPolynomialExponentialWeightedProductTruncation
