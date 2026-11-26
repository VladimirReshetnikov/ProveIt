import IPRADerivations.Analysis.Beta.GaussianEulerBetaPolynomialPrimitive
import IPRADerivations.Analysis.Exponential.GaussianPolynomialExponentialCapStability
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialRightLinearRows
import IPRADerivations.Analysis.Gamma.GaussianGammaFiniteValueProperness
import IPRADerivations.Core.CongruenceTactic
import IPRADerivations.Core.CertificateTactics

/-!
# Pascal relations for the unchanged stored Beta primitive coefficients

The original power-cap identity gives the SAME kernel's true product
successor. Its genuine right-linear convolution proves the complete
zero-extended kernel reader recurrence. The original primitive's own
stored cells are then read, including their actual outside-zero cases.
The original shifted normalized factors agree, giving the actual
primitive Pascal relation without a binomial/output identity premise.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerBetaPrimitivePascal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerBetaPolynomialPrimitive (base kernel primitive coefficient kernel_length kernel_entry_canonical)
open GaussianRationalHorner (qzero qmul qadd canonical)
open GaussianRationalMetric (qnegative qsub)
open GaussianRationalSyntheticDivision (qmul_congr qadd_congr qsub_congr)
open GaussianRationalReciprocal (qone reciprocal)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside exponent_outside)
open GaussianGammaEulerHeadShift (linear shifted)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (entry_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def reader (N e : PTm n) : PTm n := exponentCoefficient (kernel N) N e
def primitiveReader (z B N e : PTm n) : PTm n := exponentCoefficient (primitive z B N) N e
@[simp] theorem subst_reader {m : ℕ} (σ : Fin n → PTm m) (N e : PTm n) :
    Syn.subst σ (reader N e) = reader (Syn.subst σ N) (Syn.subst σ e) := by simp [reader]
@[simp] theorem subst_primitiveReader {m : ℕ} (σ : Fin n → PTm m) (z B N e : PTm n) :
    Syn.subst σ (primitiveReader z B N e) = primitiveReader (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) (Syn.subst σ e) := by simp [primitiveReader]

theorem base_leading : Γ ⊢[PRAAx] entry (base : PTm n) zero ≐ qnegative qone :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (zero_lt_succ one)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_leading _) (GaussianRationalPolynomialBuffers.pad_leading _ one zero (le_refl one))).eqTrans
      (GaussianReciprocalHorner.qadd_zero_right _ (GaussianRationalMetric.qnegative_canonical _)))
theorem base_constant : Γ ⊢[PRAAx] entry (base : PTm n) one ≐ qone :=
  (GaussianRationalPolynomialBuffers.added_lookup _ _ _ _ (le_refl two)).eqTrans
    ((qadd_congr (GaussianGammaLinearCoefficient.monomial_constant _)
      ((entry_congr (.eqRefl _) (by ipra_ring : Γ ⊢[PRAAx] one ≐ one+zero)).eqTrans
        ((GaussianRationalPolynomialBuffers.pad_tail _ one zero (lt_congr (.eqRefl _) (GaussianRationalMonicReduction.singleton_length qone).eqSymm (zero_lt_succ zero))).eqTrans
          (GaussianRationalMonicReduction.singleton_lookup qone)))).eqTrans
      (GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qone_canonical))

theorem kernel_product (N : PTm n) : Γ ⊢[PRAAx] kernel (succ N) ≐
    GaussianRationalPolynomialProduct.product (kernel N) base N one := by
  have previous := GaussianPolynomialExponentialCapStability.power_cap_identity (Γ := Γ) base one (succ N) N N (le_succ_self _) (le_refl _)
  exact (GaussianRationalPolynomialPowers.prefix_succ base one (succ N) N (le_refl (succ N))).eqTrans
    (GaussianPolynomialDeterminantTerms.product_congr previous (.eqRefl _) (by ipra_ring) (.eqRefl _))

theorem negative_one_product (x : PTm n) (hx : Γ ⊢[PRAAx] canonical x) : Γ ⊢[PRAAx] qmul x (qnegative qone) ≐ qnegative x :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianInverseBinomialRows.negative_product qone x).eqSymm.eqTrans
      (GaussianInverseBinomialRows.negative_congr ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right x hx))))

theorem kernel_leading_step (N : PTm n) : Γ ⊢[PRAAx] entry (kernel (succ N)) zero ≐ qnegative (entry (kernel N) zero) := by
  have stable := GaussianPolynomialRightLinearRows.coefficient_stabilized (Γ := Γ) (kernel N) base one (succ N) zero (zero_lt_succ N)
  have first := GaussianPolynomialLinearFactorCoefficients.first_row (Γ := Γ) (kernel N) base one zero (zero_le one)
  exact (entry_congr (kernel_product N) (.eqRefl _)).eqTrans
    ((GaussianRationalPolynomialProduct.product_lookup _ _ _ _ zero (zero_le _)).eqTrans
      (stable.eqTrans (first.eqTrans ((qmul_congr (.eqRefl _) base_leading).eqTrans (negative_one_product _ (kernel_entry_canonical N zero (zero_le N)))))))

theorem kernel_interior_step (N r : PTm n) (hr : Γ ⊢[PRAAx] le (succ r) N) : Γ ⊢[PRAAx]
    entry (kernel (succ N)) (succ r) ≐ qsub (entry (kernel N) r) (entry (kernel N) (succ r)) :=
  (entry_congr (kernel_product N) (.eqRefl _)).eqTrans
    ((GaussianPolynomialRightLinearRows.original_interior_row (kernel N) base N r hr).eqTrans
      (qadd_congr ((qmul_congr (.eqRefl _) base_constant).eqTrans (GaussianReciprocalHorner.qmul_one_right _ (kernel_entry_canonical N r (le_trans (le_succ_self r) hr))))
        ((qmul_congr (.eqRefl _) base_leading).eqTrans (negative_one_product _ (kernel_entry_canonical N (succ r) hr)))))

theorem kernel_constant_step (N : PTm n) : Γ ⊢[PRAAx] entry (kernel (succ N)) (succ N) ≐ entry (kernel N) N :=
  (entry_congr (kernel_product N) (by ipra_ring)).eqTrans
    ((GaussianPolynomialFirstCoefficients.constant_value (kernel N) base N one).eqTrans
      ((qmul_congr (.eqRefl _) base_constant).eqTrans (GaussianReciprocalHorner.qmul_one_right _ (kernel_entry_canonical N N (le_refl N)))))

theorem reader_congr {N M e f : PTm n} (hN : Γ ⊢[PRAAx] N ≐ M) (he : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx] reader N e ≐ reader M f := by
  have buffer : Γ ⊢[PRAAx] kernel N ≐ kernel M := by
    ipra_congr (kernel (var 0) : PTm 1) with [hN]
  exact GaussianRationalPolynomialExponentialStability.exponent_congr buffer hN he

theorem reader_constant_step (N : PTm n) : Γ ⊢[PRAAx] reader (succ N) zero ≐ reader N zero :=
  (exponent_inside _ _ _ (zero_le _)).eqTrans
    ((entry_congr (.eqRefl _) (monus_zero _)).eqTrans ((kernel_constant_step N).eqTrans
      ((entry_congr (.eqRefl _) (monus_zero _)).eqSymm.eqTrans (exponent_inside _ _ _ (zero_le _)).eqSymm)))

theorem index_before (N e : PTm n) (he : Γ ⊢[PRAAx] lt e N) : Γ ⊢[PRAAx] monus N e ≐ succ (monus N (succ e)) := by
  ipra_lc natEq (eq_add_of_le he)-natEq (eq_add_of_le (le_trans (le_succ_self e) he))

theorem reader_interior_step (N e : PTm n) (he : Γ ⊢[PRAAx] lt e N) : Γ ⊢[PRAAx]
    reader (succ N) (succ e) ≐ qsub (reader N (succ e)) (reader N e) := by
  let r := monus N (succ e)
  have idx := index_before N e he
  have hr : Γ ⊢[PRAAx] le (succ r) N := le_congr idx (.eqRefl _) (GaussianRationalMonicReconstruction.monus_le_left N e)
  have high : Γ ⊢[PRAAx] reader N (succ e) ≐ entry (kernel N) r := exponent_inside _ _ _ he
  have low : Γ ⊢[PRAAx] reader N e ≐ entry (kernel N) (succ r) :=
    (exponent_inside _ _ _ (le_trans (le_succ_self _) he)).eqTrans (entry_congr (.eqRefl _) idx)
  exact (exponent_inside _ _ _ (le_trans he (le_succ_self N))).eqTrans
    ((entry_congr (.eqRefl _) ((succ_monus_succ N e).eqTrans idx)).eqTrans
      ((kernel_interior_step N r hr).eqTrans (qsub_congr high.eqSymm low.eqSymm)))

theorem reader_leading (N : PTm n) : Γ ⊢[PRAAx] reader N N ≐ entry (kernel N) zero :=
  (exponent_inside _ _ _ (le_refl N)).eqTrans (entry_congr (.eqRefl _) (monus_self N))

theorem reader_leading_step (N : PTm n) : Γ ⊢[PRAAx] reader (succ N) (succ N) ≐ qsub (reader N (succ N)) (reader N N) := by
  have high : Γ ⊢[PRAAx] reader N (succ N) ≐ qzero := exponent_outside _ _ _ (le_refl (succ N))
  have leading := (reader_leading (Γ := Γ) (succ N)).eqTrans ((kernel_leading_step N).eqTrans (GaussianInverseBinomialRows.negative_congr (reader_leading N).eqSymm))
  exact leading.eqTrans ((GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical _)).eqSymm.eqTrans
    (qsub_congr high.eqSymm (.eqRefl _)))

theorem reader_outside_step (N e : PTm n) (he : Γ ⊢[PRAAx] lt N e) : Γ ⊢[PRAAx]
    reader (succ N) (succ e) ≐ qsub (reader N (succ e)) (reader N e) :=
  (exponent_outside _ _ _ ((succ_monus_succ _ _).eqTrans he)).eqTrans
    ((GaussianCoefficientNormOrder.qsub_self qzero).eqSymm.eqTrans
      (qsub_congr (exponent_outside _ _ _ (le_trans he (le_succ_self e))).eqSymm (exponent_outside _ _ _ he).eqSymm))

theorem kernel_reader_Pascal (N e : PTm n) : Γ ⊢[PRAAx] reader (succ N) (succ e) ≐ qsub (reader N (succ e)) (reader N e) := by
  refine .orE (lt_or_le e N) ?_ ?_
  · exact reader_interior_step N e Prf.hyp0
  · refine .orE (lt_or_eq_of_le Prf.hyp0) ?_ ?_
    · exact reader_outside_step N e Prf.hyp0
    · exact (reader_congr (.eqRefl _) (congrSucc Prf.hyp0.eqSymm)).eqTrans
        ((reader_leading_step N).eqTrans (qsub_congr (reader_congr (.eqRefl _) (congrSucc Prf.hyp0)) (reader_congr (.eqRefl _) Prf.hyp0)))

theorem linear_index_congr (z B e f : PTm n) (he : Γ ⊢[PRAAx] e ≐ f) : Γ ⊢[PRAAx] linear z B e ≐ linear z B f := by
  ipra_congr (linear (var 0) (var 1) (var 2) : PTm 3) with [.eqRefl z, .eqRefl B, he]

theorem primitive_reader_value (z B N e : PTm n) : Γ ⊢[PRAAx] primitiveReader z B N e ≐ qmul (reader N e) (reciprocal (linear z B e)) := by
  refine .orE (lt_or_le N e) ?_ ?_
  · exact (exponent_outside _ _ _ Prf.hyp0).eqTrans
      ((GaussianRationalSyntheticDivision.qmul_zero_left _).eqSymm.eqTrans
        (qmul_congr (exponent_outside _ _ _ Prf.hyp0).eqSymm (.eqRefl _)))
  · have low := GaussianRationalMonicReconstruction.monus_le_left (Γ := (le e N) :: Γ) N e
    exact (exponent_inside _ _ _ Prf.hyp0).eqTrans
      ((GaussianEulerBetaPolynomialPrimitive.primitive_lookup _ _ _ _ low).eqTrans
        (qmul_congr (exponent_inside _ _ _ Prf.hyp0).eqSymm
          (GaussianNameReciprocal.reciprocal_congr (linear_index_congr _ _ _ _ (GaussianRationalMonicReconstruction.complement N e Prf.hyp0)))))

theorem shifted_linear (z B e : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] linear (shifted z B) B e ≐ linear z B (succ e) :=
  GaussianGammaFiniteValueProperness.fraction_equal _ _ B hB (GaussianGammaEulerHeadShift.shifted_translation z B e)

theorem right_product_difference (a b c : PTm n) : Γ ⊢[PRAAx] qmul (qsub a b) c ≐ qsub (qmul a c) (qmul b c) :=
  (GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
    ((GaussianRationalRoundedPower.multiplication_difference c a b).eqSymm.eqTrans
      (qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _) (GaussianRationalPowerAlgebra.qmul_commutative _ _)))

/-- Actual zero-extended original primitive coefficients satisfy the
shifted Pascal relation, including all outside-degree branches. -/
theorem primitive_reader_Pascal (z B N e : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    primitiveReader z B (succ N) (succ e) ≐ qsub (primitiveReader z B N (succ e)) (primitiveReader (shifted z B) B N e) :=
  (primitive_reader_value z B (succ N) (succ e)).eqTrans
    ((qmul_congr (kernel_reader_Pascal N e) (.eqRefl _)).eqTrans
      ((right_product_difference _ _ _).eqTrans
        (qsub_congr (primitive_reader_value z B N (succ e)).eqSymm
          ((qmul_congr (.eqRefl _) (GaussianNameReciprocal.reciprocal_congr (shifted_linear z B e hB)).eqSymm).eqTrans
            (primitive_reader_value (shifted z B) B N e).eqSymm))))

theorem primitive_constant_Pascal (z B N : PTm n) : Γ ⊢[PRAAx] primitiveReader z B (succ N) zero ≐ primitiveReader z B N zero :=
  (primitive_reader_value z B (succ N) zero).eqTrans
    ((qmul_congr (reader_constant_step N) (.eqRefl _)).eqTrans (primitive_reader_value z B N zero).eqSymm)

def output (z B N e : PTm n) : PTm n := pairT (primitiveReader z B (succ N) (succ e))
  (pairT (qsub (primitiveReader z B N (succ e)) (primitiveReader (shifted z B) B N e))
    (pairT (reader (succ N) (succ e)) (qsub (reader N (succ e)) (reader N e))))
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (z B N e : PTm n) : PTm n := PTm.app outputF ![z,B,N,e]
theorem program_at (z B N e : PTm n) : Γ ⊢[PRAAx] run z B N e ≐ output z B N e := by
  simpa [run,outputF,output] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![z,B,N,e]

theorem actual_Beta_kernel_same_program_product_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
    (kernel (succ (var 0)) ≐ GaussianRationalPolynomialProduct.product (kernel (var 0)) base (var 0) one) :=
  closeUniv 1 (kernel_product _)
theorem actual_Beta_kernel_unrestricted_Pascal_reader_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (reader (succ (var 0)) (succ (var 1)) ≐ qsub (reader (var 0) (succ (var 1))) (reader (var 0) (var 1))) :=
  closeUniv 2 (kernel_reader_Pascal _ _)
theorem actual_Beta_primitive_unrestricted_Pascal_reader_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ primitiveReader (var 0) (var 1) (succ (var 2)) (succ (var 3)) ≐
      qsub (primitiveReader (var 0) (var 1) (var 2) (succ (var 3))) (primitiveReader (shifted (var 0) (var 1)) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (primitive_reader_Pascal _ _ _ _ Prf.hyp0))
theorem actual_Beta_primitive_constant_Pascal_reader_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (primitiveReader (var 0) (var 1) (succ (var 2)) zero ≐ primitiveReader (var 0) (var 1) (var 2) zero) :=
  closeUniv 3 (primitive_constant_Pascal _ _ _)
theorem actual_Beta_primitive_Pascal_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerBetaPrimitivePascal
