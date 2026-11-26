import IPRADerivations.Analysis.Polynomials.GaussianWeightedPolynomialPowerBound
import IPRADerivations.Analysis.Beta.GaussianEulerBetaPolynomialPrimitive
import IPRADerivations.AnalyticNumberTheory.BinomialThree

/-!
# Uniform weighted coefficient norm of the original beta kernel

The actual two coefficient cells of the original base are -1 and 1.
At u=a/(bN), 0<=a<=b, their computed weighted coefficient norm is
u+1<=1+1/N. The SAME original fixed-cap power buffer therefore has
weighted norm <=(1+1/N)^N<=3 by the checked native binomial theorem.
No coefficient formula, binomial expansion or norm law is a premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelWeightedNorm

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerBetaPolynomialPrimitive (base kernel base_length)
open GaussianRationalHorner (qmul qzero positive_product)
open GaussianRationalMetric (qnegative)
open GaussianRationalSyntheticDivision (qone qone_canonical qmul_congr qadd_congr)
open GaussianRationalPolynomialDilation (weightedNorm dilated dilated_lookup)
open GaussianCoefficientL1 (qL1_congr prefixNorm)
open GaussianRationalL1 (qL1)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open RationalArithmetic (add)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def argument (a b N : PTm n) : PTm n := GaussianRationalHorner.ofGaussian (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) (b*N)
@[simp] theorem subst_argument {m : ℕ} (σ : Fin n → PTm m) (a b N : PTm n) :
    Syn.subst σ (argument a b N) = argument (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by simp [argument]

theorem base_leading : Γ ⊢[PRAAx] entry (base : PTm n) zero ≐ qnegative qone := by
  have constant : Γ ⊢[PRAAx] entry (GaussianGammaEulerFactorPolynomial.constant : PTm n) zero ≐ qzero :=
    GaussianRationalPolynomialBuffers.pad_leading _ one zero (le_refl one)
  exact (GaussianRationalPolynomialBuffers.added_lookup _ _ two zero (le_succ_self one)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_leading _) constant).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalMetric.qnegative_canonical _)))

theorem base_constant : Γ ⊢[PRAAx] entry (base : PTm n) one ≐ qone := by
  have constant : Γ ⊢[PRAAx] entry (GaussianGammaEulerFactorPolynomial.constant : PTm n) one ≐ qone :=
    (LeanProofs.IPRA.Foundations.SequenceComposition.entry_congr (.eqRefl _) (add_zero one).eqSymm).eqTrans
      ((GaussianRationalPolynomialBuffers.pad_tail _ one zero
        (lt_congr (.eqRefl _) (GaussianRationalMonicReduction.singleton_length qone).eqSymm (le_refl one))).eqTrans
          (GaussianRationalMonicReduction.singleton_lookup qone))
  exact (GaussianRationalPolynomialBuffers.added_lookup _ _ two one (le_refl two)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_constant _) constant).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ qone_canonical))

theorem argument_norm (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qL1 (argument a b N) ≐ fraction a (b*N) :=
  GaussianFiniteLogarithmWeightedNorm.l1_from_representation _ (ComplexLogarithmRemainder.scale a ComplexLogarithmRemainder.oneCode) a (b*N)
    (positive_product _ _ hb hN) (GaussianRationalHorner.ofGaussian_represents _ _ (positive_product _ _ hb hN))
    ((GaussianL1.norm1_scale _ _).eqTrans ((congrMul (.eqRefl _) GaussianL1.norm1_one).eqTrans (by ipra_ring)))

/-- Exact original two-cell weighted norm, with the real zero case retained. -/
theorem base_norm (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    weightedNorm base one (argument a b N) ≐ add (fraction a (b*N)) (fraction one one) := by
  let u := argument a b N
  let C := dilated base one u
  have canonical : Γ ⊢[PRAAx] GaussianRationalHorner.canonical u :=
    GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ hb hN)
  have unit : Γ ⊢[PRAAx] qmul qone u ≐ u :=
    (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right u canonical)
  have leading : Γ ⊢[PRAAx] entry C zero ≐ qnegative u :=
    (dilated_lookup base one u zero (zero_le one)).eqTrans
      ((qmul_congr base_leading ((congrAp2 GaussianRationalReciprocal.powerF (monus_zero one) (.eqRefl _)).eqTrans
        (GaussianRationalPowerAlgebra.power_one u canonical))).eqTrans
          ((GaussianInverseBinomialRows.negative_product qone u).eqSymm.eqTrans (GaussianInverseBinomialRows.negative_congr unit)))
  have constant : Γ ⊢[PRAAx] entry C one ≐ qone :=
    (dilated_lookup base one u one (le_refl one)).eqTrans
      ((qmul_congr base_constant ((congrAp2 GaussianRationalReciprocal.powerF (monus_self one) (.eqRefl _)).eqTrans
        (GaussianRationalReciprocal.power_zero u))).eqTrans (GaussianReciprocalHorner.qmul_one_right qone qone_canonical))
  have first : Γ ⊢[PRAAx] prefixNorm C one ≐ fraction a (b*N) :=
    (GaussianCoefficientL1.prefix_succ C zero).eqTrans
      ((RationalAlgebra.add_congr ((GaussianCoefficientL1.prefix_zero C).eqTrans GaussianRationalLinearProduct.scalar_zero_code.eqSymm)
        ((qL1_congr leading).eqTrans ((GaussianRationalL1Algebra.qL1_negative u).eqTrans (argument_norm a b N hb hN)))).eqTrans
          (GaussianRationalLinearProduct.scalar_zero_add _ (RationalNormalForm.normalize_well_formed _ _ (positive_product _ _ hb hN))))
  exact (GaussianRationalLinearProduct.norm_length C (succ one) (GaussianRationalPolynomialDilation.dilated_length _ _ _)).eqTrans
    ((GaussianCoefficientL1.prefix_succ C one).eqTrans
      (RationalAlgebra.add_congr first ((qL1_congr constant).eqTrans GaussianRationalSyntheticBounds.qL1_qone)))

theorem unit_sum (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    add (fraction one N) (fraction one one) ≐ fraction (succ N) N := by
  have rep := RationalRepresentations.represents_add _ _ _ _ _ _ (fraction_represents one N hN) (fraction_represents one one (le_refl one))
  exact RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hN) rep (fraction_represents (succ N) N hN)
    (positive_product _ _ hN (le_refl one)) hN (by
      apply ZT.derive
      simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
      ipra_simps
      ring)

theorem base_bound (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm base one (argument a b N)) (fraction (succ N) N) := by
  have small := fraction_order a (b*N) one N (positive_product _ _ hb hN) hN
    (le_congr (mul_comm _ _) (by ipra_ring) (mul_le_mul_right N ha))
  exact RationalArgmin.rationalLE_congr (base_norm a b N hb hN).eqSymm (unit_sum N hN)
    (GaussianRationalSyntheticBounds.add_monotone _ _ _ _ small (RationalArgmin.reflexive _))

theorem binomial_budget (N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    rationalLE (RationalNonnegativePowers.power (succ N) N N) (fraction (LeanProofs.IPRA.PTm.num 3) one) :=
  GaussianRationalMetric.comparison_of_cleared _ _ (pw (succ N) N) (LeanProofs.IPRA.PTm.num 3) (pw N N) one
    (RationalNonnegativePowers.denominator_positive N N hN) (le_refl one)
    (RationalNonnegativePowers.power_represents _ _ _ hN) (fraction_represents _ _ (le_refl one))
    (le_congr (one_mul _).eqSymm (.eqRefl _) (AnalyticNumberTheory.BinomialThree.binomial_three N))

/-- Uniform in the actual degree N and including a=0. The coefficient
buffer is literally the original stored beta kernel (1-X)^N. -/
theorem original_kernel_weighted_norm (a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N)
    (ha : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    rationalLE (weightedNorm (kernel N) N (argument a b N)) (fraction (LeanProofs.IPRA.PTm.num 3) one) := by
  have original := GaussianWeightedPolynomialPowerBound.power_bound base one N (argument a b N) (succ N) N N
    (by simpa using (base_length (Γ := Γ))) hN (base_bound a b N hb hN ha) (le_refl N)
  have normalized := RationalArgmin.rationalLE_congr
    (GaussianFiniteExponentialWeightedNorm.weighted_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] N*one ≐ N) (.eqRefl _)) (.eqRefl _) original
  exact RationalArgmin.transitive normalized (binomial_budget N hN)

theorem original_beta_base_weighted_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2) ⋏ le (var 0) (var 1)) ⟶
      rationalLE (weightedNorm base one (argument (var 0) (var 1) (var 2))) (fraction (succ (var 2)) (var 2))) :=
  closeUniv 3 (.impI (base_bound _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))
theorem original_beta_kernel_uniform_weighted_norm_three_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((le one (var 1) ⋏ le one (var 2) ⋏ le (var 0) (var 1)) ⟶
      rationalLE (weightedNorm (kernel (var 2)) (var 2) (argument (var 0) (var 1) (var 2))) (fraction (LeanProofs.IPRA.PTm.num 3) one)) :=
  closeUniv 3 (.impI (original_kernel_weighted_norm _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelWeightedNorm
