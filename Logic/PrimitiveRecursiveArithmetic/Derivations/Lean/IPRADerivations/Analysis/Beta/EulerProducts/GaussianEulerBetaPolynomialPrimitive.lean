import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Coefficients.GaussianGammaEulerFactorPolynomial
import IPRADerivations.Analysis.Polynomials.Coefficients.Operations.GaussianRationalEulerCoefficients
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.GaussianGammaEulerHeadShift
import IPRADerivations.Analysis.Gamma.EulerProducts.FiniteHeads.Denominators.GaussianGammaEulerHeadLower
import IPRADerivations.Analysis.Polynomials.Translation.GaussianInverseBinomialRows
import IPRADerivations.Analysis.Polynomials.Products.LinearFactors.GaussianPolynomialLinearFactorCoefficients

/-!
# A literal finite Beta primitive for arbitrary complex rational exponents

The actual stored kernel is the old polynomial power (1-X)^N. The new
stored primitive divides its exponent-j cell by the original normalized
linear factor z/B+j. Its actual weighted Euler buffer multiplies each
stored cell by that SAME factor. Native pole guards derive every inverse
identity, so the weighted buffer has exactly the old kernel's coefficients
and Horner value. Formally this is (z/B+X*d/dX)P=(1-X)^N, the finite
algebra behind d(t^(z/B)P)/dt=t^(z/B-1)(1-t)^N.

No integral or analytic derivative is defined here. The value at one,
its rising-product formula, finite quadrature errors and the lower
endpoint estimate are separate obligations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaPolynomialPrimitive

open_ipra
open GaussianRationalHorner (qmul qadd canonical evaluate represents positive_product)
open GaussianRationalMetric (qnegative qsub)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr canonicalCoefficients)
open GaussianRationalReciprocal (qone reciprocal power)
open GaussianGammaEulerHeadShift (linear)
open GaussianGammaEulerHeadLower (poleGuard pole_at translated)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry sequence sequence_length sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceComposition (length entry_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def base : PTm n := GaussianRationalPolynomialBuffers.added
  (GaussianGammaLinearCoefficient.monomial (qnegative qone)) GaussianGammaEulerFactorPolynomial.constant two
def kernel (N : PTm n) : PTm n := GaussianRationalPolynomialPowers.power base one N

def data (z B N : PTm n) : PTm n := pairT z (pairT B N)
def coefficient (z B N i : PTm n) : PTm n :=
  qmul (entry (kernel N) i) (reciprocal (linear z B (monus N i)))
def rowBody : PTm 2 := coefficient (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def primitive (z B N : PTm n) : PTm n := sequence rowBody (succ N) (data z B N)
def weightedCoefficient (z B N i : PTm n) : PTm n :=
  qmul (linear z B (monus N i)) (entry (primitive z B N) i)
def weightedRow : PTm 2 := weightedCoefficient (fstT (var 1)) (fstT (sndT (var 1))) (sndT (sndT (var 1))) (var 0)
def weighted (z B N : PTm n) : PTm n := sequence weightedRow (succ N) (data z B N)
def source (z B A N : PTm n) : Fm PTm n := le one B ⋏ (le one A ⋏ poleGuard z B one A N)

ipra_subst base
ipra_subst kernel
ipra_subst data
ipra_subst coefficient
ipra_subst primitive
ipra_subst weightedCoefficient
ipra_subst weighted
ipra_subst source

theorem base_length : Γ ⊢[PRAAx] length (base : PTm n) ≐ two := GaussianRationalPolynomialBuffers.added_length _ _ _
theorem kernel_length (N : PTm n) : Γ ⊢[PRAAx] length (kernel N) ≐ succ N :=
  (GaussianRationalPolynomialPowers.power_length base one N).eqTrans (congrSucc (by ipra_ring))
theorem kernel_canonical (N : PTm n) : Γ ⊢[PRAAx] canonicalCoefficients (kernel N) := GaussianRationalPolynomialPowers.power_canonical _ _ _
theorem kernel_entry_canonical (N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] canonical (entry (kernel N) i) :=
  GaussianRationalSyntheticDivision.canonical_coefficient_at _ _ (kernel_canonical N)
    (lt_congr (.eqRefl _) (kernel_length N).eqSymm ((succ_monus_succ _ _).eqTrans hi))

theorem base_evaluation (t : PTm n) (ht : Γ ⊢[PRAAx] canonical t) : Γ ⊢[PRAAx] evaluate base t ≐ qsub qone t := by
  have unit : Γ ⊢[PRAAx] qmul qone t ≐ t := (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right t ht)
  have neg : Γ ⊢[PRAAx] qmul (qnegative qone) t ≐ qnegative t :=
    (GaussianInverseBinomialRows.negative_product qone t).eqSymm.eqTrans (GaussianInverseBinomialRows.negative_congr unit)
  exact (GaussianRationalPolynomialBuffers.added_evaluation _ _ _ _ (GaussianGammaLinearCoefficient.monomial_length _) GaussianGammaEulerFactorPolynomial.constant_length).eqTrans
    ((qadd_congr ((GaussianGammaLinearCoefficient.monomial_evaluation _ _).eqTrans neg) (GaussianGammaEulerFactorPolynomial.constant_evaluation t)).eqTrans
      (GaussianReciprocalHorner.qadd_commutative _ _))

theorem kernel_evaluation (N t : PTm n) (ht : Γ ⊢[PRAAx] canonical t) : Γ ⊢[PRAAx]
    evaluate (kernel N) t ≐ power (qsub qone t) N :=
  (GaussianRationalPolynomialPowers.power_evaluation base one N t (by simpa using (base_length (Γ := Γ)))).eqTrans
    (congrAp2 GaussianRationalReciprocal.powerF (.eqRefl N) (base_evaluation t ht))

theorem coefficient_congr {z z' B B' N N' i i' : PTm n} (hz : Γ ⊢[PRAAx] z ≐ z') (hB : Γ ⊢[PRAAx] B ≐ B')
    (hN : Γ ⊢[PRAAx] N ≐ N') (hi : Γ ⊢[PRAAx] i ≐ i') : Γ ⊢[PRAAx] coefficient z B N i ≐ coefficient z' B' N' i' := by
  ipra_congr (coefficient (var 0) (var 1) (var 2) (var 3) : PTm 4) with [hz, hB, hN, hi]

theorem row_at (z B N i : PTm n) : Γ ⊢[PRAAx] inst2 rowBody i (data z B N) ≐ coefficient z B N i := by
  simp only [rowBody,inst2,subst_coefficient,subst_fstT,subst_sndT,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one]
  exact coefficient_congr (fst_pair _ _) (snd_pair _ _).fstE (snd_pair _ _).sndE (.eqRefl _)
theorem primitive_length (z B N : PTm n) : Γ ⊢[PRAAx] length (primitive z B N) ≐ succ N := sequence_length _ _ _
theorem primitive_lookup (z B N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] entry (primitive z B N) i ≐ coefficient z B N i :=
  (sequence_decode rowBody ((succ_monus_succ _ _).eqTrans hi)).eqTrans (row_at z B N i)
theorem primitive_entry_canonical (z B N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] canonical (entry (primitive z B N) i) :=
  GaussianRationalHorner.canonical_congr (primitive_lookup z B N i hi) (GaussianRationalHorner.qmul_canonical _ _)

theorem linear_inverse (z B A N j : PTm n) (h : Γ ⊢[PRAAx] source z B A N) (hj : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx]
    qmul (linear z B j) (reciprocal (linear z B j)) ≐ qone := by
  have lower := GaussianRationalLowerBounds.lower_from_representation (linear z B j) (translated z B j) B one A h.andE₁ h.andE₂.andE₁
    (GaussianRationalHorner.ofGaussian_represents _ _ h.andE₁)
    (le_congr (by ipra_ring) (.eqRefl _) (pole_at z B one A N j h.andE₂.andE₂ hj))
  exact GaussianRationalReciprocal.reciprocal_identity _ (GaussianNameReciprocal.lower_norm_positive _ A h.andE₂.andE₁
    (GaussianRationalLowerBounds.name_lower _ one A (le_refl one) h.andE₂.andE₁ lower))

theorem weighted_coefficient (z B A N i : PTm n) (h : Γ ⊢[PRAAx] source z B A N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    weightedCoefficient z B N i ≐ entry (kernel N) i := by
  have inverse := linear_inverse z B A N (monus N i) h (GaussianRationalMonicReconstruction.monus_le_left _ _)
  exact (qmul_congr (.eqRefl _) (primitive_lookup z B N i hi)).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
      ((GaussianReciprocalHorner.qmul_associative _ _ _).eqTrans
        ((qmul_congr (.eqRefl _) ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans inverse)).eqTrans
          (GaussianReciprocalHorner.qmul_one_right _ (kernel_entry_canonical N i hi)))))

theorem weighted_row_at (z B N i : PTm n) : Γ ⊢[PRAAx] inst2 weightedRow i (data z B N) ≐ weightedCoefficient z B N i := by
  simpa [weightedRow,inst2,data] using Prf.eqCongr
    (weightedCoefficient (var 0) (var 1) (var 2) (var 3) : PTm 4)
    (σ := ![fstT (data z B N),fstT (sndT (data z B N)),sndT (sndT (data z B N)),i]) (σ' := ![z,B,N,i])
    (fun k => by
      fin_cases k
      · exact fst_pair _ _
      · exact (snd_pair _ _).fstE
      · exact (snd_pair _ _).sndE
      · exact .eqRefl _)
theorem weighted_length (z B N : PTm n) : Γ ⊢[PRAAx] length (weighted z B N) ≐ succ N := sequence_length _ _ _
theorem weighted_lookup (z B N i : PTm n) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (weighted z B N) i ≐ weightedCoefficient z B N i :=
  (sequence_decode weightedRow ((succ_monus_succ _ _).eqTrans hi)).eqTrans (weighted_row_at z B N i)

theorem weighted_entries (z B A N : PTm n) (h : Γ ⊢[PRAAx] source z B A N) : Γ ⊢[PRAAx]
    .all (lt (var 0) (succ (Syn.shift N)) ⟶ entry (weighted (Syn.shift z) (Syn.shift B) (Syn.shift N)) (var 0) ≐ entry (kernel (Syn.shift N)) (var 0)) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift B) (Syn.shift A) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  have hi : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  exact (weighted_lookup _ _ _ _ hi).eqTrans (weighted_coefficient _ _ (Syn.shift A) _ _ hs.wk hi)

theorem weighted_evaluation (z B A N t : PTm n) (h : Γ ⊢[PRAAx] source z B A N) : Γ ⊢[PRAAx]
    evaluate (weighted z B N) t ≐ evaluate (kernel N) t := by
  have rows : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ N)) ⟶ entry (Syn.shift (weighted z B N)) (var 0) ≐ entry (Syn.shift (kernel N)) (var 0)) :=
    by simpa [Syn.shift] using weighted_entries z B A N h
  exact (congrAp3 GaussianRationalHorner.hornerF (weighted_length z B N) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ t (succ N) (succ N) rows (le_refl _)).eqTrans
      (congrAp3 GaussianRationalHorner.hornerF (kernel_length N).eqSymm (.eqRefl _) (.eqRefl _)))

theorem beta_polynomial_primitive (z B A N t : PTm n) (h : Γ ⊢[PRAAx] source z B A N) (ht : Γ ⊢[PRAAx] canonical t) : Γ ⊢[PRAAx]
    evaluate (weighted z B N) t ≐ power (qsub qone t) N :=
  (weighted_evaluation z B A N t h).eqTrans (kernel_evaluation N t ht)

/-- The multiplier is the original normalized rational z/B+j, rather
than a separately supplied formal coefficient. -/
theorem linear_as_sum (z B j : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    linear z B j ≐ qadd (GaussianRationalHorner.ofGaussian z B) (GaussianRationalNaturalScale.naturalPoint j) := by
  have hr : Γ ⊢[PRAAx] represents (GaussianRationalNaturalScale.naturalPoint j)
      (ComplexLogarithmRemainder.scale (B*j) ComplexLogarithmRemainder.oneCode) B :=
    GaussianRationalHorner.represents_congr (.eqRefl _) (by
      apply GaussianRootAlgebra.equal_of_values <;>
        simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale] <;> ipra_simps <;> ring)
      (by ipra_ring) (GaussianRationalHorner.represents_rescale _ _ one B (GaussianRationalNaturalScale.natural_point_represents j))
  exact GaussianRationalHorner.canonical_unique _ _ _ _ (GaussianRationalHorner.ofGaussian_canonical _ _ hB)
    (GaussianRationalHorner.qadd_canonical _ _) hB (GaussianRationalHorner.ofGaussian_represents _ _ hB)
    (GaussianRationalHorner.qadd_represents _ _ _ _ _ hB (GaussianRationalHorner.ofGaussian_represents z B hB) hr)

theorem actual_euler_row (z B N i : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    weightedCoefficient z B N i ≐ qadd
      (qmul (GaussianRationalHorner.ofGaussian z B) (entry (primitive z B N) i))
      (GaussianRationalNaturalScale.natScale (monus N i) (entry (primitive z B N) i)) :=
  (qmul_congr (linear_as_sum z B (monus N i) hB) (.eqRefl _)).eqTrans
    ((GaussianRationalPolynomialBuffers.distribute_right _ _ _).eqTrans
      (qadd_congr (.eqRefl _) (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm))

/-- The unchanged original scalar-product, Euler and sum programs form
the actual coefficient buffer (z/B+X*d/dX)P. -/
def eulerOperator (z B N : PTm n) : PTm n := GaussianRationalPolynomialBuffers.added
  (GaussianRationalPolynomialProduct.product (GaussianRationalMonicReduction.singleton (GaussianRationalHorner.ofGaussian z B)) (primitive z B N) zero N)
  (GaussianRationalEulerCoefficients.euler (primitive z B N) N) (succ N)
ipra_subst eulerOperator
theorem operator_length (z B N : PTm n) : Γ ⊢[PRAAx] length (eulerOperator z B N) ≐ succ N := GaussianRationalPolynomialBuffers.added_length _ _ _
theorem operator_lookup (z B A N i : PTm n) (h : Γ ⊢[PRAAx] source z B A N) (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    entry (eulerOperator z B N) i ≐ entry (kernel N) i :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ ((succ_monus_succ _ _).eqTrans hi)).eqTrans
    ((qadd_congr (GaussianPolynomialLinearFactorCoefficients.constant_left_value _ _ N i hi)
      (GaussianRationalEulerCoefficients.euler_lookup _ N i hi)).eqTrans
        ((actual_euler_row z B N i h.andE₁).eqSymm.eqTrans (weighted_coefficient z B A N i h hi)))

theorem operator_evaluation (z B A N t : PTm n) (h : Γ ⊢[PRAAx] source z B A N) (ht : Γ ⊢[PRAAx] canonical t) : Γ ⊢[PRAAx]
    evaluate (eulerOperator z B N) t ≐ power (qsub qone t) N := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift B) (Syn.shift A) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  have rows : Γ ⊢[PRAAx] .all (lt (var 0) (Syn.shift (succ N)) ⟶ entry (Syn.shift (eulerOperator z B N)) (var 0) ≐ entry (Syn.shift (kernel N)) (var 0)) := by
    refine .allI (.impI ?_)
    have hi : (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
      (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    simpa only [Syn.shift,ConciseIPRA.PTm.subst_succ,subst_eulerOperator,subst_kernel] using
      operator_lookup (Syn.shift z) (Syn.shift B) (Syn.shift A) (Syn.shift N) (var 0) hs.wk hi
  exact (congrAp3 GaussianRationalHorner.hornerF (operator_length z B N) (.eqRefl _) (.eqRefl _)).eqTrans
    ((GaussianRationalLinearProduct.horner_ext _ _ t (succ N) (succ N) rows (le_refl _)).eqTrans
      ((congrAp3 GaussianRationalHorner.hornerF (kernel_length N).eqSymm (.eqRefl _) (.eqRefl _)).eqTrans (kernel_evaluation N t ht)))

def output (z B N t : PTm n) : PTm n := pairT (primitive z B N)
  (pairT (eulerOperator z B N) (pairT (evaluate (eulerOperator z B N) t) (power (qsub qone t) N)))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z B N t : PTm n) : PTm n := PTm.app outputF ![z,B,N,t]
theorem program_at (z B N t : PTm n) : Γ ⊢[PRAAx] run z B N t ≐ output z B N t := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,B,N,t]

theorem actual_Beta_primitive_cell_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 2) (var 3) ⋏ le (var 4) (var 3)) ⟶
      entry (eulerOperator (var 0) (var 1) (var 3)) (var 4) ≐ entry (kernel (var 3)) (var 4)) :=
  closeUniv 5 (.impI (operator_lookup _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_Beta_polynomial_primitive_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((source (var 0) (var 1) (var 2) (var 3) ⋏ canonical (var 4)) ⟶
      evaluate (eulerOperator (var 0) (var 1) (var 3)) (var 4) ≐ power (qsub qone (var 4)) (var 3)) :=
  closeUniv 5 (.impI (operator_evaluation _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_Beta_kernel_value_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (canonical (var 1) ⟶ evaluate (kernel (var 0)) (var 1) ≐ power (qsub qone (var 1)) (var 0)) :=
  closeUniv 2 (.impI (kernel_evaluation _ _ Prf.hyp0))
theorem actual_Beta_primitive_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

theorem base_constant : Γ ⊢[PRAAx] entry (base : PTm n) one ≐ qone :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (le_refl two)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_constant _)
      ((entry_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] one ≐ one+zero)).eqTrans
        ((GaussianRationalPolynomialBuffers.pad_tail _ one zero (Order.zero_lt_of_eq_succ (GaussianRationalMonicReduction.singleton_length qone))).eqTrans
          (GaussianRationalMonicReduction.singleton_lookup qone)))).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qone_canonical))

theorem base_leading : Γ ⊢[PRAAx] entry (base : PTm n) zero ≐ qnegative qone :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (zero_lt_succ one)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_leading _) (GaussianRationalPolynomialBuffers.pad_leading _ one zero (le_refl one))).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalMetric.qnegative_canonical _)))

end LeanProofs.IPRA.Analysis.GaussianEulerBetaPolynomialPrimitive
