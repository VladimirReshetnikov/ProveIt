import IPRADerivations.Algebra.QuadraticRationalRadicandOrder
import IPRADerivations.Algebra.QuadraticRationalEmbedding

/-!
# Scalar embedding and the root at an actual positive rational radicand

The original scalar pair and the original root pair are used without a
change to their representation. The computed positive rational reduction
supplies the order reflection and the sign of the root. The literal pair
product of the root with itself represents the original rational radicand.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Algebra.QuadraticRationalRadicandEmbedding

open_ipra
open LeanProofs.IPRA.Analysis
open RationalSupMetric (numeratorOf denominatorOf)
open RationalArgmin (rationalEq rationalEq_congr left)
open RationalAlgebra (positive_product)
open QuadraticRationalRadicand (isPositive integerRadicand changeBasis sign equivalent less multiply
  positiveNumerator rescale stretch stretch_first stretch_second equal_from_representations equal_pairs_from_representations)
open QuadraticRationalRadicandOrder (positive same_coefficients_equivalent)
open QuadraticRationalEmbedding (embed root)
open QuadraticRationalClearing (represents sameCoefficients)
open QuadraticSignCertificates (first second equal first_value second_value)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem divide_congr (q x y : PTm n) (hq : Γ ⊢[PRAAx] le one q) (h : Γ ⊢[PRAAx] rationalEq x y) : Γ ⊢[PRAAx]
    rationalEq (QuadraticRationalRadicand.divideBy x q) (QuadraticRationalRadicand.divideBy y q) := by
  refine equal_from_representations _ _ _ _ _ _ (positive_product (RationalArgmin.denominator_positive x) hq)
    (positive_product (RationalArgmin.denominator_positive y) hq)
    (QuadraticRationalRadicand.divide_represents _ _ _ _ hq (RationalRepresentations.represents_self x))
    (QuadraticRationalRadicand.divide_represents _ _ _ _ hq (RationalRepresentations.represents_self y)) ?_
  apply ZT.derive
  have he := natEq h
  simp only [RationalArgmin.left,Q.mk_add,Q.mk_mul,map_add,map_mul] at he
  simp only [ZT.toZ_mul,ZT.toZ_ofNat,Q.mk_mul,map_mul]
  simp only [ZT.toZ]
  linear_combination 𝔞(q) * he

theorem rescale_congr (q x y : PTm n) (hq : Γ ⊢[PRAAx] le one q) (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx]
    sameCoefficients (rescale q x) (rescale q y) :=
  .andI (rationalEq_congr (fst_pair _ _).eqSymm (fst_pair _ _).eqSymm (.andE₁ h))
    (rationalEq_congr (snd_pair _ _).eqSymm (snd_pair _ _).eqSymm (divide_congr _ _ _ hq (.andE₂ h)))

theorem coefficients_equivalent (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d)
    (h : Γ ⊢[PRAAx] sameCoefficients x y) : Γ ⊢[PRAAx] equivalent d x y :=
  (QuadraticRationalRadicand.equivalent_iff d x y hd).iffMpr (same_coefficients_equivalent _ _ _
    (QuadraticRationalRadicand.integer_radicand_positive d hd) (rescale_congr _ _ _ (RationalArgmin.denominator_positive d) h))

theorem scalar_change_basis (q x : PTm n) (hq : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx]
    sameCoefficients (rescale q (embed x)) (embed x) := by
  let A := QuadraticIntegerEmbedding.integer (numeratorOf x)
  let D := denominatorOf x
  have hx := QuadraticRationalEmbedding.original_embedding_represents (Γ := Γ) x
  apply equal_pairs_from_representations _ _ _ _ _ _
    (positive_product (RationalArgmin.denominator_positive x) hq) (RationalArgmin.denominator_positive x)
    (QuadraticRationalRadicand.rescale_represents _ _ A D hq hx) hx
  · simp only [stretch_first,Q.mk_mul,map_mul]; ring
  · simp only [stretch_second,A,QuadraticIntegerEmbedding.integer_second]
    ring

private theorem basis_scalar_equivalent (d x : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    QuadraticRationalEqualityOrder.equivalent (integerRadicand d) (changeBasis d (embed x)) (embed x) :=
  same_coefficients_equivalent _ _ _ (QuadraticRationalRadicand.integer_radicand_positive d hd)
    (scalar_change_basis _ _ (RationalArgmin.denominator_positive d))

theorem embedding_injective_iff (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    Fm.iff (equivalent d (embed x) (embed y)) (rationalEq x y) := by
  have pos := QuadraticRationalRadicand.integer_radicand_positive d hd
  have hx := basis_scalar_equivalent d x hd
  have hy := basis_scalar_equivalent d y hd
  have ee := QuadraticRationalRadicand.equivalent_iff d (embed x) (embed y) hd
  have ei := QuadraticRationalEmbedding.embedding_injective_iff (integerRadicand d) x y pos
  refine .andI (.impI ?_) (.impI ?_)
  · exact ei.wk.iffMp (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ pos.wk
      (QuadraticRationalEqualityOrder.equivalent_symm _ _ _ pos.wk hx.wk)
      (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ pos.wk (ee.wk.iffMp Prf.hyp0) hy.wk))
  · exact ee.wk.iffMpr (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ pos.wk hx.wk
      (QuadraticRationalEqualityOrder.equivalent_trans _ _ _ _ pos.wk (ei.wk.iffMpr Prf.hyp0)
        (QuadraticRationalEqualityOrder.equivalent_symm _ _ _ pos.wk hy.wk)))

theorem embedding_order_iff (d x y : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    Fm.iff (less d (embed x) (embed y)) (lt (left x y) (left y x)) := by
  have pos := QuadraticRationalRadicand.integer_radicand_positive d hd
  have hx := basis_scalar_equivalent d x hd
  have hy := basis_scalar_equivalent d y hd
  have el := QuadraticRationalRadicand.less_iff d (embed x) (embed y) hd
  have ei := QuadraticRationalEmbedding.embedding_order_iff (integerRadicand d) x y pos
  refine .andI (.impI ?_) (.impI ?_)
  · exact ei.wk.iffMp (QuadraticRationalEqualityOrder.less_congr _ _ _ _ _ pos.wk hx.wk hy.wk
      (el.wk.iffMp Prf.hyp0))
  · exact el.wk.iffMpr (QuadraticRationalEqualityOrder.less_congr _ _ _ _ _ pos.wk
      (QuadraticRationalEqualityOrder.equivalent_symm _ _ _ pos.wk hx.wk)
      (QuadraticRationalEqualityOrder.equivalent_symm _ _ _ pos.wk hy.wk) (ei.wk.iffMpr Prf.hyp0))

theorem root_positive (d : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx] positive d (root : PTm n) := by
  let q := denominatorOf d
  have hq := RationalArgmin.denominator_positive (Γ := Γ) d
  have pos := QuadraticRationalRadicand.integer_radicand_positive d hd
  have rep := QuadraticRationalRadicand.rescale_represents q root QuadraticIntegerOrder.root one hq QuadraticRationalEmbedding.root_represents
  have eq : Γ ⊢[PRAAx] equal (stretch q QuadraticIntegerOrder.root) QuadraticIntegerOrder.root := by
    apply QuadraticConeOrder.equal_of_values
    · simp only [stretch_first,QuadraticIntegerOrder.root,QuadraticSignCertificates.naturalPair,first_value,ZT.toZ_ofNat,
        Q.mk_zero,map_zero]
      ring
    · exact stretch_second _ _
  have rootRep := QuadraticRationalEqualityOrder.represents_native_congr _ _ _ _ rep eq
  exact (QuadraticRationalClearing.representation_sign _ _ _ _ pos (positive_product (le_refl one) hq) rootRep).eqTrans
    (QuadraticIntegerOrder.root_positive _ pos)

theorem root_square (d : PTm n) (hd : Γ ⊢[PRAAx] isPositive d) : Γ ⊢[PRAAx]
    equivalent d (multiply d root root) (embed d) := by
  let q := denominatorOf d
  let p := positiveNumerator d
  have hq := RationalArgmin.denominator_positive (Γ := Γ) d
  have hOne : Γ ⊢[PRAAx] le one one := le_refl one
  have lhs := QuadraticRationalRadicand.multiply_represents d root root QuadraticIntegerOrder.root QuadraticIntegerOrder.root one one
    hd hOne hOne QuadraticRationalEmbedding.root_represents QuadraticRationalEmbedding.root_represents
  have rhs := QuadraticRationalEmbedding.embedding_represents d q (ZT.ofNat p) (QuadraticRationalRadicand.radicand_represents d hd)
  apply coefficients_equivalent _ _ _ hd
  apply equal_pairs_from_representations _ _ _ _ _ _ (positive_product hq (positive_product hOne hOne)) hq lhs rhs
  · simp only [QuadraticRationalRadicand.product_numerator_first,QuadraticIntegerOrder.root,
      QuadraticSignCertificates.naturalPair,first_value,second_value,QuadraticIntegerEmbedding.integer_first,
      ZT.toZ_ofNat,Q.mk_mul,map_mul,Q.mk_zero,map_zero,Q.mk_one,map_one]
    ring
  · simp only [QuadraticRationalRadicand.product_numerator_second,QuadraticIntegerOrder.root,
      QuadraticSignCertificates.naturalPair,first_value,second_value,QuadraticIntegerEmbedding.integer_second,
      ZT.toZ_ofNat,Q.mk_zero,map_zero,Q.mk_one,map_one]
    ring

theorem actual_positive_rational_root_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (isPositive (var 0) ⟶ (positive (var 0) root ⋏ equivalent (var 0) (multiply (var 0) root root) (embed (var 0)))) :=
  closeUniv 1 (.impI (.andI (root_positive _ Prf.hyp0) (root_square _ Prf.hyp0)))

theorem actual_rational_radicand_scalar_embedding_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (isPositive (var 0) ⟶ (Fm.iff (equivalent (var 0) (embed (var 1)) (embed (var 2))) (rationalEq (var 1) (var 2))) ⋏
      Fm.iff (less (var 0) (embed (var 1)) (embed (var 2))) (lt (left (var 1) (var 2)) (left (var 2) (var 1)))) :=
  closeUniv 3 (.impI (.andI (embedding_injective_iff _ _ _ Prf.hyp0) (embedding_order_iff _ _ _ Prf.hyp0)))

end LeanProofs.IPRA.Algebra.QuadraticRationalRadicandEmbedding
