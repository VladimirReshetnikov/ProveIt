import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail26Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail26_merge_certificate :
    table0Tail26Candidate = table0Tail26Normal := by
  decide

theorem table0_tail26_certificate :
    SparsePolynomial.substitute table0Tail26 elementaryPolynomials = table0Tail26Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-192, ⟨1, 0, 1, 5, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨3125, ⟨1, 0, 1, 0, 4⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨7500, ⟨1, 0, 0, 2, 3⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-27, ⟨0, 7, 0, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail27 elementaryPolynomials)))) = table0Tail26Normal
  rw [table0_term104_certificate, table0_term105_certificate, table0_term106_certificate, table0_term107_certificate, table0_tail27_certificate]
  exact table0_tail26_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
