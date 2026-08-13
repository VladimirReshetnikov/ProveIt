import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail30Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail30_merge_certificate :
    table0Tail30Candidate = table0Tail30Normal := by
  decide

theorem table0_tail30_certificate :
    SparsePolynomial.substitute table0Tail30 elementaryPolynomials = table0Tail30Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨65, ⟨0, 2, 4, 2, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-725, ⟨0, 2, 2, 1, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-160, ⟨0, 2, 1, 3, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-192, ⟨0, 2, 0, 5, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail31 elementaryPolynomials)))) = table0Tail30Normal
  rw [table0_term120_certificate, table0_term121_certificate, table0_term122_certificate, table0_term123_certificate, table0_tail31_certificate]
  exact table0_tail30_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
