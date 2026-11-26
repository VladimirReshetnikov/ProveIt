import IPRADerivations.Analysis.Beta.GaussianBetaKernelWeightedNorm
import IPRADerivations.Analysis.Polynomials.GaussianEuclideanPolynomialMajorant
import IPRADerivations.Analysis.Beta.GaussianEulerBetaPoleGuard
import IPRADerivations.Analysis.Gamma.Zeta.GaussianGammaZetaCoefficientNorm

/-!
# The actual beta primitive has the uniform compact bound 3A

At 0<=u=a/(bN)<=1/N, the actual weighted kernel coefficient norm is
at most three. The original positive real-part margin bounds every
actual reciprocal z/B+j by A in Euclidean norm. Their original stored
coefficient products therefore sum to a Euclidean bound 3A, uniformly
in the internal degree N. No primitive-output budget is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveUniformBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerBetaPolynomialPrimitive (primitive primitive_length primitive_lookup coefficient kernel)
open GaussianGammaEulerHeadShift (linear)
open GaussianBetaKernelWeightedNorm (argument)
open GaussianRationalPolynomialDilation (dilated dilated_lookup dilated_length weightedNorm)
open GaussianRationalHorner (qmul positive_product evaluate)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalL1 (qL1)
open GaussianRationalSumMajorant (majorized majorized_congr)
open GaussianCoefficientL1 (prefixNorm)
open GaussianPositiveRealArithmetic (sign)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z B A : PTm n) : Fm PTm n := le one B ⋏ le one A ⋏ GaussianEulerLowerPowerCoefficients.realLower z A B
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z B A : PTm n) :
    (source z B A).subst σ = source (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ A) := by simp [source]

/-- The actual reciprocal bound is Euclidean, with no factor two loss. -/
theorem reciprocal_bound (z B A j : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    bounded (reciprocal (linear z B j)) A one := by
  have lower := GaussianRationalLowerBounds.lower_from_representation (linear z B j)
    (GaussianGammaEulerHeadLower.translated z B j) B one A h.andE₁ h.andE₂.andE₁
    (GaussianRationalHorner.ofGaussian_represents _ _ h.andE₁)
    (le_congr (by ipra_ring) (.eqRefl _) (GaussianEulerBetaPoleGuard.pole_at_every_index z B A j h.andE₂.andE₂))
  exact GaussianRationalLowerBounds.inverse_bound _ one A (le_refl one) h.andE₂.andE₁ lower

theorem reciprocal_majorized (z B A j : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    majorized (reciprocal (linear z B j)) (fraction A one) :=
  GaussianRationalSumMajorant.from_representation _ _ A one (le_refl one)
    (GaussianRationalL1.nonnegative_of_representation _ _ _ (le_refl one) (fraction_represents A one (le_refl one)))
    (fraction_represents A one (le_refl one)) (reciprocal_bound z B A j h)

/-- Original primitive cells, weighted at the actual argument, retain
the SAME original weighted kernel cells and actual reciprocal factors. -/
theorem weighted_coefficient (z B N u i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (dilated (primitive z B N) N u) i ≐
      qmul (entry (dilated (kernel N) N u) i) (reciprocal (linear z B (monus N i))) :=
  (dilated_lookup _ N u i hi).eqTrans
    ((qmul_congr (primitive_lookup z B N i hi) (.eqRefl _)).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)).eqTrans
          ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
            (qmul_congr (dilated_lookup (kernel N) N u i hi).eqSymm (.eqRefl _))))))

theorem weighted_cell_majorized (z B A N u i : PTm n) (h : Γ ⊢[PRAAx] source z B A)
    (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    majorized (entry (dilated (primitive z B N) N u) i)
      (RationalArithmetic.multiply (fraction A one) (qL1 (entry (dilated (kernel N) N u) i))) :=
  majorized_congr (weighted_coefficient z B N u i hi).eqSymm (RationalAlgebra.multiply_commutative _ _)
    (GaussianRationalSumMajorant.majorized_multiply _ _ _ _
      (GaussianEuclideanPolynomialMajorant.l1_majorized _) (reciprocal_majorized z B A (monus N i) h))

theorem weighted_entries_majorized (z B A N u : PTm n) (h : Γ ⊢[PRAAx] source z B A) : Γ ⊢[PRAAx]
    GaussianEuclideanPolynomialMajorant.entriesMajorized (dilated (primitive z B N) N u)
      (dilated (kernel N) N u) (fraction A one) (succ N) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift B) (Syn.shift A) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans (Prf.hyp0 (Γ := Γ.map Fm.shift) (φ := lt (var 0) (succ (Syn.shift N))))
  simpa only [Δ,GaussianEuclideanPolynomialMajorant.entriesMajorized,GaussianRationalPolynomialDilation.subst_dilated,
    GaussianEulerBetaPolynomialPrimitive.subst_primitive,GaussianEulerBetaPolynomialPrimitive.subst_kernel,
    GaussianEuclideanDistanceName.subst_fraction,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift] using
    weighted_cell_majorized (Syn.shift z) (Syn.shift B) (Syn.shift A) (Syn.shift N) (Syn.shift u) (var 0)
      hs.wk hi

theorem original_primitive_majorized (z B A N a b : PTm n) (h : Γ ⊢[PRAAx] source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    majorized (evaluate (primitive z B N) (argument a b N))
      (RationalArithmetic.multiply (fraction A one) (weightedNorm (kernel N) N (argument a b N))) := by
  let u := argument a b N
  let C := dilated (primitive z B N) N u
  let D := dilated (kernel N) N u
  have sum := GaussianEuclideanPolynomialMajorant.horner_majorized C D (fraction A one) (succ N)
    (weighted_entries_majorized z B A N u h)
  have norm := (GaussianRationalLinearProduct.norm_length (Γ := Γ) D (succ N) (dilated_length _ _ _)).eqSymm
  have scalar := RationalAlgebra.multiply_congr (.eqRefl (fraction A one)) norm
  have atOne : Γ ⊢[PRAAx] GaussianRationalHorner.horner C qone (succ N) ≐ evaluate C qone :=
    congrAp3 GaussianRationalHorner.hornerF (dilated_length _ _ _).eqSymm (.eqRefl _) (.eqRefl _)
  have original : Γ ⊢[PRAAx] evaluate C qone ≐ evaluate (primitive z B N) u :=
    (GaussianRationalPolynomialDilation.dilation_evaluation _ _ u qone (primitive_length z B N)).eqTrans
      (GaussianRationalMonicReduction.evaluate_congr (.eqRefl _)
        (GaussianReciprocalHorner.qmul_one_right u (GaussianRationalHorner.ofGaussian_canonical _ _ (positive_product _ _ hb hN))))
  exact majorized_congr (atOne.eqTrans original) scalar sum

/-- Uniform in numerical N and arbitrary raw native z. The positive
margin is the original source inequality B<=A*Re(z). -/
theorem original_primitive_bound (z B A N a b : PTm n) (h : Γ ⊢[PRAAx] source z B A)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) (ha : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    bounded (evaluate (primitive z B N) (argument a b N)) ((LeanProofs.IPRA.PTm.num 3)*A) one := by
  let r := RationalArithmetic.multiply (fraction A one) (weightedNorm (kernel N) N (argument a b N))
  have actual := original_primitive_majorized z B A N a b h hb hN
  have bound := RationalArithmetic.multiply_monotone (fraction A one) _ _
    (GaussianRationalL1.nonnegative_of_representation _ _ _ (le_refl one) (fraction_represents A one (le_refl one)))
    (GaussianBetaKernelWeightedNorm.original_kernel_weighted_norm a b N hb hN ha)
  have scalarBound : Γ ⊢[PRAAx] RationalArgmin.rationalLE r (fraction ((LeanProofs.IPRA.PTm.num 3)*A) one) :=
    RationalArgmin.rationalLE_congr (.eqRefl _) ((RationalNonnegativePowers.fraction_multiply A one (LeanProofs.IPRA.PTm.num 3) one (le_refl one) (le_refl one)).eqTrans
      (RationalNonnegativePowers.fraction_congr (by ipra_ring) (by ipra_ring))) bound
  have embedded := GaussianCoefficientNormEntries.l1_to_euclidean (RationalGaussianEmbedding.embed r) ((LeanProofs.IPRA.PTm.num 3)*A) one (le_refl one)
    (RationalArgmin.rationalLE_congr (GaussianGammaZetaCoefficientNorm.nonnegative_embed_norm r actual.andE₁ (RationalArithmetic.multiply_guard _ _)).eqSymm (.eqRefl _) scalarBound)
  exact GaussianRationalSumMajorant.majorant_bound _ r _ one (le_refl one) actual embedded

theorem original_beta_primitive_uniform_threeA_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((source (var 0) (var 1) (var 2) ⋏ le one (var 5) ⋏ le one (var 3) ⋏ le (var 4) (var 5)) ⟶
      bounded (evaluate (primitive (var 0) (var 1) (var 3)) (argument (var 4) (var 5) (var 3))) ((LeanProofs.IPRA.PTm.num 3)*var 2) one) :=
  closeUniv 6 (.impI (original_primitive_bound _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaPrimitiveUniformBound
