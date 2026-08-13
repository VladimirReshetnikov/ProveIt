import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail27Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail27_merge_certificate :
    table0Tail27Candidate = table0Tail27Normal := by
  decide

theorem table0_tail27_certificate :
    SparsePolynomial.substitute table0Tail27 elementaryPolynomials = table0Tail27Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨18, ⟨0, 6, 1, 1, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-4, ⟨0, 6, 0, 3, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-4, ⟨0, 5, 3, 0, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨1, ⟨0, 5, 2, 2, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail28 elementaryPolynomials)))) = table0Tail27Normal
  rw [table0_term108_certificate, table0_term109_certificate, table0_term110_certificate, table0_term111_certificate, table0_tail28_certificate]
  exact table0_tail27_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
