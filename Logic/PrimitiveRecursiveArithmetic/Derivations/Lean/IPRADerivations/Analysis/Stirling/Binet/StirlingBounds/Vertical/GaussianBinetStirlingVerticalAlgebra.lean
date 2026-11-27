import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.Vertical.GaussianBinetLogVerticalStep
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingSlopeBound
import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.GaussianBinetStirlingUnitDifference
import IPRADerivations.Analysis.Polynomials.Coefficients.GaussianRationalCoefficientScaling

/-!
# Algebra of a literal vertical Stirling step

At arbitrary rational samples, the two Stirling constants cancel and
the weighted logarithm difference has the exact product decomposition.
Substituting the actual logarithm and log-Gamma linear terms leaves
the vertical displacement times the first-order Stirling expression.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalAlgebra

open_ipra
open GaussianBinetLogVerticalStep (step native_displacement)
open GaussianBinetStirlingRemainder (offset)
open GaussianBinetStirlingUnitDifferenceAlgebra (rawCore rawRemainder)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNameArithmetic (sum_difference)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalCoefficientScaling (qmul_add)
open GaussianRationalDistanceOrder (reversed_difference)
open GaussianRationalHorner (canonical_unique ofGaussian_canonical ofGaussian_represents qadd qmul qzero represents_congr)
open GaussianRationalMetric (qnegative qnegative_canonical qsub qsub_canonical qsub_represents)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalPowerDifference (product_difference)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalSumAlgebra (qadd_associative)
open GaussianRationalSyntheticDivision (qadd_congr qadd_sub_cancel qmul_congr qone qsub_congr)
open GaussianReciprocalHorner (qadd_commutative qadd_zero_right qmul_associative qmul_one_right)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem displacement (A B D sign H : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] qsub (argument A (B+H) D sign) (argument A B D sign) ≐ step H D sign := by
  let a := native A (B+H) sign
  let b := native A B sign
  let c := native zero H sign
  have hd := h.andE₂
  have diff := qsub_represents _ _ a b D hd (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  exact canonical_unique _ _ c D (qsub_canonical _ _) (ofGaussian_canonical _ _ hd) hd
    (represents_congr (.eqRefl _) (native_displacement A B sign H h.andE₁.andE₂) (.eqRefl _) diff)
    (ofGaussian_represents _ _ hd)

private theorem subtract_difference (a b c d : PTm n) : Γ ⊢[PRAAx]
    qsub (qsub a b) (qsub c d) ≐ qsub (qsub a c) (qsub b d) := by
  change Γ ⊢[PRAAx] qsub (qadd a (qnegative b)) (qadd c (qnegative d)) ≐ qadd (qsub a c) (qnegative (qsub b d))
  exact (sum_difference a c (qnegative b) (qnegative d)).eqTrans
    (qadd_congr (.eqRefl _) (GaussianCharacteristicEntryNorm.negative_difference b d))

private theorem offset_displacement (A B D sign H : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] qsub (offset A (B+H) D sign) (offset A B D sign) ≐ step H D sign := by
  let a := argument A (B+H) D sign
  let b := argument A B D sign
  let r := qnegative (fraction (one : PTm n) two)
  have folded := sum_difference (Γ := Γ) a b r r
  exact folded.eqTrans ((qadd_congr (displacement A B D sign H h) (GaussianCoefficientNormOrder.qsub_self r)).eqTrans
    (qadd_zero_right _ (ofGaussian_canonical _ _ h.andE₂)))

theorem remainder_difference (A B D sign H g l k m c : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx] qsub (rawRemainder A (B+H) D sign k m c) (rawRemainder A B D sign g l c) ≐
      qadd (qsub (qsub k g) (qadd (qmul (step H D sign) m) (qmul (offset A B D sign) (qsub m l))))
        (step H D sign) := by
  let z := argument A B D sign
  let w := argument A (B+H) D sign
  let u := offset A B D sign
  let v := offset A (B+H) D sign
  let a := rawCore A B D sign g l
  let b := rawCore A (B+H) D sign k m
  have ec : Γ ⊢[PRAAx] qsub (qsub b c) (qsub a c) ≐ qsub b a :=
    (sum_difference b a (qnegative c) (qnegative c)).eqTrans
      ((qadd_congr (.eqRefl _) (GaussianCoefficientNormOrder.qsub_self _)).eqTrans
        (qadd_zero_right _ (qsub_canonical _ _)))
  have prod := (product_difference (Γ := Γ) v u m l).eqTrans
    (qadd_congr (qmul_congr (offset_displacement A B D sign H h) (.eqRefl _)) (.eqRefl _))
  exact ec.eqTrans ((sum_difference (qsub k (qmul v m)) (qsub g (qmul u l)) w z).eqTrans
    (qadd_congr ((subtract_difference k (qmul v m) g (qmul u l)).eqTrans (qsub_congr (.eqRefl _) prod))
      (displacement A B D sign H h)))

private theorem mul_sub (a b c : PTm n) : Γ ⊢[PRAAx] qmul a (qsub b c) ≐ qsub (qmul a b) (qmul a c) :=
  (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference a b c).eqSymm

private theorem add_back (a b : PTm n) (ha : Γ ⊢[PRAAx] GaussianRationalHorner.canonical a) :
    Γ ⊢[PRAAx] qadd (qsub a b) b ≐ a := by
  have neg : Γ ⊢[PRAAx] qsub qzero b ≐ qnegative b :=
    (qadd_commutative _ _).eqTrans (qadd_zero_right _ (qnegative_canonical b))
  have cancel := (qadd_congr (.eqRefl b) neg.eqSymm).eqTrans (GaussianNameRingLaws.additive_inverse_value b)
  change Γ ⊢[PRAAx] qadd (qadd a (qnegative b)) b ≐ a
  exact (qadd_associative _ _ _).eqTrans
    ((qadd_congr (.eqRefl _) ((qadd_commutative _ _).eqTrans cancel)).eqTrans (qadd_zero_right a ha))

private theorem regroup (g l c : PTm n) :
    Γ ⊢[PRAAx] qadd (qsub g (qadd l (qsub qone c))) qone ≐ qadd (qsub g l) c := by
  let d := qsub qone c
  let v := qadd l d
  have e : Γ ⊢[PRAAx] qsub v l ≐ d := qadd_sub_cancel l d (qsub_canonical _ _)
  exact (qadd_congr (.eqRefl _) (add_back qone c GaussianRationalSyntheticDivision.qone_canonical).eqSymm).eqTrans
    ((qadd_associative _ _ _).eqSymm.eqTrans
      (qadd_congr ((qadd_congr (.eqRefl _) e.eqSymm).eqTrans (GaussianReconstructionRoots.difference_chain g v l))
        (.eqRefl _)))

theorem linear_expression (A B D sign H g l : PTm n) (h : Γ ⊢[PRAAx] source A D sign) :
    Γ ⊢[PRAAx]
      qadd (qsub (qmul (step H D sign) g)
        (qadd (qmul (step H D sign) l) (qmul (offset A B D sign) (qmul (step H D sign) (reciprocal (argument A B D sign))))))
        (step H D sign) ≐
      qmul (step H D sign) (qadd (qsub g l) (GaussianBinetStirlingSlopeBound.correction A B D sign)) := by
  let z := argument A B D sign
  let e := step H D sign
  let b := fraction (one : PTm n) two
  let w := reciprocal z
  let u := offset A B D sign
  have hNorm := GaussianNameReciprocal.lower_norm_positive z D h.andE₂
    (GaussianRationalLowerBounds.name_lower z A D h.andE₁.andE₁ h.andE₂
      (GaussianBinetReciprocalRows.real_part_lower A B D sign h))
  have inv := GaussianRationalReciprocal.reciprocal_identity z hNorm
  have o : Γ ⊢[PRAAx] qmul u w ≐ qsub qone (qmul b w) :=
    (qmul_commutative u w).eqTrans ((mul_sub w z b).eqTrans
      (qsub_congr ((qmul_commutative w z).eqTrans inv) (qmul_commutative w b)))
  have inner : Γ ⊢[PRAAx] qmul u (qmul e w) ≐ qmul e (qsub qone (qmul b w)) :=
    (qmul_associative _ _ _).eqSymm.eqTrans ((qmul_congr (qmul_commutative u e) (.eqRefl w)).eqTrans
      ((qmul_associative _ _ _).eqTrans (qmul_congr (.eqRefl _) o)))
  have ecanon : Γ ⊢[PRAAx] GaussianRationalHorner.canonical e := ofGaussian_canonical _ _ h.andE₂
  exact (qadd_congr (qsub_congr (.eqRefl _) ((qadd_congr (.eqRefl _) inner).eqTrans (qmul_add _ _ _).eqSymm))
      (qmul_one_right e ecanon).eqSymm).eqTrans
    ((qadd_congr (mul_sub _ _ _).eqSymm (.eqRefl _)).eqTrans
      ((qmul_add _ _ _).eqSymm.eqTrans (qmul_congr (.eqRefl _) (regroup g l (qmul b w)))))

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingVerticalAlgebra
