import IPRADerivations.Analysis.Series.Bernoulli.BernoulliBounds
import IPRADerivations.Analysis.RationalArithmetic.GoldenRatio.RationalPhiSharpQuintic
import IPRADerivations.Analysis.Polynomials.CompanionMatrices.GaussianPolynomialMonicCompanion
import IPRADerivations.Analysis.Exponential.FiniteSeries.Products.GaussianRationalFiniteExponentialEuler

/-!
# The fixed-order multiplicative Stirling coefficients

Quote the Bernoulli log coefficients at each externally fixed order
as an exact rational polynomial. Run the original primitive-recursive
finite exponential on that buffer and read its low coefficients.
The Euler derivative identity of the returned polynomial gives the
Stirling coefficient recurrence in object iPRA.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingExpansionCoefficients

open_ipra
open BernoulliBounds (zint)
open BernoulliCoefficients (bc)
open GaussianPolynomialMonicCompanion (normalizedRow normalized_length normalized_canonical)
open GaussianRationalHorner (canonical ofGaussian ofGaussian_canonical qzero)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient)
open GaussianRationalNaturalScale (natScale)
open GaussianRationalPolynomialExponential (polynomial)
open GaussianRationalPolynomialProduct (product)
open GaussianRationalSyntheticDivision (qone qzero_canonical)
open GaussianRationalEulerCoefficients (euler)
open RationalGaussianEmbedding (native)
open RationalPhiSharpQuintic (buffer buffer_length buffer_lookup numeral_lt numeral_le)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The coefficient of y^j in the logarithmic Stirling polynomial,
where y=1/x and the normalized Bernoulli polynomial is B_k/k!. -/
def logCoefficient (j : ℕ) : ℚ :=
  if j % 2 = 1 then ((j-1).factorial : ℚ)*bc (j+1) 0 else 0

theorem log_coefficient_even (r : ℕ) : logCoefficient (2*r) = 0 := by
  simp [logCoefficient]

theorem log_coefficient_odd (r : ℕ) : logCoefficient (2*r+1) =
    ((2*r+2).factorial : ℚ)*bc (2*r+2) 0 / ((2*(r : ℚ)+2)*(2*(r : ℚ)+1)) := by
  have odd : (2*r+1)%2 = 1 := by omega
  rw [logCoefficient,if_pos odd]
  simp only [Nat.add_sub_cancel]
  rw [show 2*r+2 = (2*r+1)+1 by omega, Nat.factorial_succ, Nat.factorial_succ (2*r)]
  push_cast
  have h₁ : 2*(r : ℚ)+2 ≠ 0 := by positivity
  have h₂ : 2*(r : ℚ)+1 ≠ 0 := by positivity
  field_simp
  ring

def quoted (q : ℚ) : PTm n :=
  if q = 0 then qzero else ofGaussian (native (zint q.num)) (num q.den)

theorem quoted_canonical (q : ℚ) : Γ ⊢[PRAAx] canonical (quoted q) := by
  unfold quoted
  split
  · exact qzero_canonical
  · exact ofGaussian_canonical _ _ (numeral_le 1 q.den q.den_pos)

def literalTable (m : ℕ) : PTm n :=
  buffer (List.ofFn (fun j : Fin (m+1) => quoted (logCoefficient (m-j.val))))

def logTable (m : ℕ) : PTm n := normalizedRow (literalTable m)

theorem literal_length (m : ℕ) : Γ ⊢[PRAAx] length (literalTable m : PTm n) ≐ succ (num m) := by
  have h : Γ ⊢[PRAAx] length (literalTable m : PTm n) ≐ num (m+1) := by
    simpa only [literalTable,List.length_ofFn] using buffer_length (Γ := Γ)
      (List.ofFn (fun j : Fin (m+1) => quoted (logCoefficient (m-j.val))) : List (PTm n))
  exact h.eqTrans (by apply deriveNat; ipra_simps; simp [Nat.cast_add])

theorem log_table_length (m : ℕ) : Γ ⊢[PRAAx] length (logTable m : PTm n) ≐ succ (num m) :=
  (normalized_length _).eqTrans (literal_length m)

theorem log_table_canonical (m : ℕ) : Γ ⊢[PRAAx] GaussianRationalSyntheticDivision.canonicalCoefficients (logTable m : PTm n) :=
  normalized_canonical (literalTable m)

theorem log_table_entry (m j : ℕ) (h : j ≤ m) :
    Γ ⊢[PRAAx] entry (logTable m) (num j) ≐ quoted (logCoefficient (m-j)) := by
  have hlt : Γ ⊢[PRAAx] lt (num j) (length (literalTable m)) :=
    lt_congr (.eqRefl _) (literal_length m).eqSymm (numeral_lt j (m+1) (by omega))
  have read : Γ ⊢[PRAAx] entry (literalTable m) (num j) ≐ quoted (logCoefficient (m-j)) := by
    have e := buffer_lookup (Γ := Γ) (List.ofFn (fun k : Fin (m+1) => quoted (logCoefficient (m-k.val)))) j
      (by simpa using Nat.lt_succ_of_le h)
    simpa only [literalTable,List.getElem_ofFn] using e
  exact (GaussianRationalCoefficientScaling.scaled_lookup _ _ _ hlt).eqTrans
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl qone) read).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans
        (GaussianReciprocalHorner.qmul_one_right _ (quoted_canonical _))))

theorem log_table_zero (m : ℕ) : Γ ⊢[PRAAx] entry (logTable m) (num m) ≐ qzero := by
  simpa [logCoefficient,quoted] using log_table_entry (Γ := Γ) m m (Nat.le_refl _)

def expTable (m : ℕ) : PTm n :=
  polynomial (logTable m) (num m) (num m)
def expCoeff (m : ℕ) (j : PTm n) : PTm n :=
  exponentCoefficient (expTable m) (num m*num m) j
def eulerProductCoeff (m : ℕ) (j : PTm n) : PTm n :=
  exponentCoefficient (product (euler (logTable m) (num m)) (expTable m)
    (num m) (num m*num m)) (num m+num m*num m) j

/-- Degree j of yP'(y) is j times the degree-j coefficient. Thus
the degree-j coefficient of (yL'(y))P(y) is the required convolution. -/
theorem exp_coefficient_recurrence (m : ℕ) (j : PTm n) (hj : Γ ⊢[PRAAx] le j (num m)) :
    Γ ⊢[PRAAx] natScale j (expCoeff m j) ≐ eulerProductCoeff m j :=
  GaussianRationalFiniteExponentialEuler.finite_euler_scaled _ _ _ _ (log_table_length m)
    (log_table_canonical m) (log_table_zero m) hj hj

theorem actual_Stirling_multiplicative_coefficient_recurrence_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1
      (le (var 0) (num m) ⟶ natScale (var 0) (expCoeff m (var 0)) ≐ eulerProductCoeff m (var 0)) :=
  closeUniv 1 (.impI (exp_coefficient_recurrence m _ Prf.hyp0))

theorem exp_coefficient_zero (m : ℕ) : Γ ⊢[PRAAx] expCoeff m zero ≐ qone := by
  let L := logTable (n := n) m
  let M : PTm n := num m
  have first := GaussianRationalPolynomialExponentialCoefficients.finite_low_expansion (Γ := Γ) L M M zero
    (log_table_zero m) (zero_le M) (zero_le M)
  have initial := GaussianRationalPolynomialExponentialCoefficients.sum_zero (Γ := Γ) L M M zero
  have value := GaussianRationalPolynomialExponentialCoefficients.coefficient_zero (Γ := Γ) L M M zero
  have exponent : Γ ⊢[PRAAx] exponentCoefficient
        (GaussianRationalPolynomialPowers.powerPrefix L M M zero) (zero*M) zero ≐ qone := by
    refine (GaussianRationalPolynomialExponentialStability.exponent_congr
      (GaussianRationalPolynomialPowers.prefix_zero L M M) (zero_mul M) (.eqRefl zero)).eqTrans ?_
    exact (GaussianRationalLowCoefficientConvolution.exponent_inside _ _ _ (le_refl zero)).eqTrans
      ((LeanProofs.IPRA.Foundations.SequenceComposition.entry_congr (.eqRefl _) (monus_zero zero)).eqTrans
        (GaussianRationalMonicReduction.singleton_lookup qone))
  have tail := (GaussianRationalSyntheticDivision.qmul_congr
    (GaussianRationalPolynomialExponential.inverse_factorial_zero (Γ := Γ)) exponent).eqTrans
      (GaussianPolynomialDeterminantTerms.one_mul_canonical qone GaussianRationalSyntheticDivision.qone_canonical)
  exact first.eqTrans (initial.eqSymm.eqTrans (value.eqTrans tail))

@[simp] theorem subst_quoted {k : ℕ} (σ : Fin n → PTm k) (q : ℚ) :
    Syn.subst σ (quoted q) = quoted q := by
  unfold quoted
  split <;> simp [native,zint]

private theorem subst_buffer {k : ℕ} (σ : Fin n → PTm k) (xs : List (PTm n)) :
    Syn.subst σ (buffer xs) = buffer (xs.map (Syn.subst σ)) := by
  induction xs <;> simp [buffer, *]

@[simp] theorem subst_literalTable {k : ℕ} (σ : Fin n → PTm k) (m : ℕ) :
    Syn.subst σ (literalTable m) = literalTable m := by
  simp only [literalTable,subst_buffer,List.map_ofFn]
  congr 2
  funext j
  exact subst_quoted σ _

ipra_subst logTable

ipra_subst expTable

end LeanProofs.IPRA.Analysis.GaussianStirlingExpansionCoefficients
