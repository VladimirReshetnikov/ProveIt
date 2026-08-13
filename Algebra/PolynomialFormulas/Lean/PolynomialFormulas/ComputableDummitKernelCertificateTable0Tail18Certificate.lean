import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail18Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail18_merge_certificate :
    table0Tail18Candidate = table0Tail18Normal := by
  decide

theorem table0_tail18_certificate :
    SparsePolynomial.substitute table0Tail18 elementaryPolynomials = table0Tail18Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨5, ⟨2, 1, 4, 2, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨1995, ⟨2, 1, 2, 1, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-1174, ⟨2, 1, 1, 3, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-16, ⟨2, 1, 0, 5, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail19 elementaryPolynomials)))) = table0Tail18Normal
  rw [table0_term72_certificate, table0_term73_certificate, table0_term74_certificate, table0_term75_certificate, table0_tail19_certificate]
  exact table0_tail18_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
