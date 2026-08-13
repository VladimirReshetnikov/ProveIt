import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail22Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail22_merge_certificate :
    table0Tail22Candidate = table0Tail22Normal := by
  decide

theorem table0_tail22_certificate :
    SparsePolynomial.substitute table0Tail22 elementaryPolynomials = table0Tail22Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨15, ⟨1, 3, 1, 1, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-384, ⟨1, 3, 0, 3, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨1, ⟨1, 2, 5, 1, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨525, ⟨1, 2, 3, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail23 elementaryPolynomials)))) = table0Tail22Normal
  rw [table0_term88_certificate, table0_term89_certificate, table0_term90_certificate, table0_term91_certificate, table0_tail23_certificate]
  exact table0_tail22_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
