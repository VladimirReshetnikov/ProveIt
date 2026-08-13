import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail29Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail29_merge_certificate :
    table0Tail29Candidate = table0Tail29Normal := by
  decide

theorem table0_tail29_certificate :
    SparsePolynomial.substitute table0Tail29 elementaryPolynomials = table0Tail29Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨12, ⟨0, 3, 3, 1, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-128, ⟨0, 3, 2, 3, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨1200, ⟨0, 3, 0, 2, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-12, ⟨0, 2, 5, 0, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail30 elementaryPolynomials)))) = table0Tail29Normal
  rw [table0_term116_certificate, table0_term117_certificate, table0_term118_certificate, table0_term119_certificate, table0_tail30_certificate]
  exact table0_tail29_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
