import DiophantineConsistency.SplitKernels59
open DiophantineConsistency SplitCertificate59 SplitKernels59
#print axioms D0_eq
#print axioms D1_eq
#print axioms D2_eq
#print axioms sourcePolynomial_eq
#print axioms coeff_sourcePolynomial
#print axioms sourcePolynomial_zero_iff
#print axioms degree_encoded
#print axioms degree_sourcePolynomial
#print axioms kernelBounds_pow
#print axioms source_one_not_zero
#print axioms source_zero_has_nonzero_digit

example (ports : Fin 4 → ℤ) :
    (D2 ports).coeff 1929 = 1 := SplitKernelData59.leading_D2 ports

-- The new whole54 box uses the sharp even kappa scale (864014+12=864026).
example (ports : Fin 4 → ℤ)
    (hb : 0 ≤ ports 0 ∧ ports 0 < 2^429959)
    (hk : 0 ≤ ports 1 ∧ ports 1 < 2^434054)
    (hm : 0 ≤ ports 2 ∧ ports 2 < 2^429959)
    (hf : 0 ≤ ports 3 ∧ ports 3 < 2*2^429959) :
    SplitWordBounds.KernelBounds (D0 ports) (D1 ports) (D2 ports) (2^864014) :=
  kernelBounds_pow ports 429959 434054 (by decide) (by decide) hb hk hm hf

example (ports : Fin 4 → ℤ) : sourceRows ports (fun _ => 1) 9 = -7 :=
  source_one_not_zero ports
