import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalHeadUniformMass
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.ProductCoefficients.GaussianBarnesCanonicalTaylorProductCoefficientName

/-!
# Disk-uniform size of the actual stored Barnes Taylor coefficient

Use the original centered head mass and the actual exponential prefix
mass at each requested order. The original convolution bounds every
retained coefficient by the same number at every finite cutoff and
prefactor precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductUniformMass

open_ipra
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_length buffer_canonical)
open GaussianBarnesCanonicalExponentTaylorMass (massCap mass)
open GaussianBarnesCanonicalExponentTaylorRetainedCoefficient (cutoff precision)
open GaussianBarnesCanonicalHeadUniformMass (headCap head_mass)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProduct (headPolynomial headDegree)
open GaussianBarnesCanonicalTaylorProductCoefficientCauchy (productCoefficient exponentPrefix)
open GaussianBarnesCanonicalTaylorProductCoefficientName (clock nameF data sample_at)
open GaussianCoefficientL1 (coefficientNorm qL1_congr)
open GaussianNamedMultiplyRate (sampleBound)
open GaussianRationalL1 (qL1)
open GaussianRationalMetric (bounded)
open GaussianRationalPolynomialExponentialProductTruncation (exponential_prefix_mass exponential_prefix_length)
open GaussianRationalPolynomialProduct (product product_length)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticBounds (natCode)
open RationalArgmin (rationalLE rationalLE_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cap (R M : PTm n) : PTm n := headCap R*pw (num 3) (massCap R M)

@[simp] theorem subst_cap {l : ℕ} (σ : Fin n → PTm l) (R M : PTm n) :
    Syn.subst σ (cap R M) = cap (Syn.subst σ R) (Syn.subst σ M) := by
  simp [cap,massCap,GaussianBarnesCanonicalExponentTaylorMass.coefficientCap,
    GaussianBarnesCanonicalExponentTaylorMass.linearCap,GaussianBarnesCanonicalExponentTaylorMass.squareCap,
    GaussianBarnesCanonicalExponentTaylorMass.stirlingCap,GaussianBarnesCanonicalExponentTaylorMass.quadraticCap,
    GaussianBarnesCanonicalExponentTaylorMass.halfCap,GaussianBarnesCanonicalPrefactor.quadraticCoefficientData,
    GaussianBarnesCanonicalPrefactor.negativeHalf,pw,one,two]

theorem coefficient_mass (q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) : Γ ⊢[PRAAx] rationalLE (qL1 (productCoefficient q z R B r M e)) (natCode (cap R M)) := by
  let N := previous M
  let P := headPolynomial z R B
  let E := exponentPrefix q z R B r M
  let K := headDegree R
  let C := buffer q z R B r M
  have hN : Γ ⊢[PRAAx] le N (N*N) :=
    le_congr (one_mul N) (.eqRefl _) (mul_le_mul_right N (zero_lt_succ (succ M)))
  have eMass : Γ ⊢[PRAAx] rationalLE (coefficientNorm E) (natCode (pw (num 3) (massCap R M))) :=
    exponential_prefix_mass C N N N (massCap R M)
      (buffer_length q z R B r M) (buffer_canonical q z R B r M) hN (mass q z R B r M hz)
  have pMass : Γ ⊢[PRAAx] rationalLE (coefficientNorm (product P E K N)) (natCode (cap R M)) :=
    GaussianRationalPolynomialProductTruncation.factor_mass P E K N (headCap R) (pw (num 3) (massCap R M))
      (GaussianBarnesCanonicalCenteredHead.polynomial_length z B (initial R)) (exponential_prefix_length C N N N)
      (head_mass z R B hz) eMass
  have hi := GaussianRationalMonicReconstruction.monus_le_left (Γ := Γ) (K+N) e
  have inside := lt_congr (.eqRefl _) (product_length P E K N).eqSymm ((succ_monus_succ _ _).eqTrans hi)
  exact rationalLE_congr
    (qL1_congr (GaussianRationalPolynomialExponentialProductTruncation.coefficient P C K N N e he)).eqSymm
    (.eqRefl _) (RationalArgmin.transitive (GaussianCoefficientNormEntries.coefficient_entry_bound _ _ inside) pMass)

theorem raw_bound (q z R B r M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) : Γ ⊢[PRAAx] bounded (productCoefficient q z R B r M e) (cap R M) one :=
  GaussianCoefficientNormEntries.l1_to_euclidean _ _ _ (le_refl one) (coefficient_mass q z R B r M e hz he)

theorem cofinal_samples (z R B M e : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (he : Γ ⊢[PRAAx] le e (previous M)) : Γ ⊢[PRAAx] sampleBound nameF (data z R B M e) (cap R M) := by
  refine .allI ?_
  let a (u : PTm n) := Syn.shift u
  let t := clock (var 0) (a z) (a R) (a B) (a M) (a e)
  have hzs : Γ.map Fm.shift ⊢[PRAAx] source (a z) (a R) (a B) := by simpa [Fm.shift,Syn.shift,a] using hz.shift
  have hes : Γ.map Fm.shift ⊢[PRAAx] le (a e) (previous (a M)) := by simpa [Fm.shift,Syn.shift,a] using he.shift
  simpa only [sampleBound,a,Syn.shift,subst_cap,GaussianBarnesCanonicalTaylorProductCoefficientName.subst_data] using
    bound_congr (sample_at (var 0) (a z) (a R) (a B) (a M) (a e)).eqSymm (.eqRefl _) (.eqRefl _)
      (raw_bound (precision t (a R)) (a z) (a R) (a B) (cutoff t (a R) (a M)) (a M) (a e) hzs hes)

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductUniformMass
