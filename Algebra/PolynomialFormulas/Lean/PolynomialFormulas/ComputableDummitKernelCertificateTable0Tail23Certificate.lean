import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail23Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail23_merge_certificate :
    table0Tail23Candidate = table0Tail23Normal := by
  decide

theorem table0_tail23_certificate :
    SparsePolynomial.substitute table0Tail23 elementaryPolynomials = table0Tail23Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-528, ⟨1, 2, 2, 2, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨384, ⟨1, 2, 1, 4, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-1750, ⟨1, 2, 0, 1, 3⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-29, ⟨1, 1, 4, 1, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail24 elementaryPolynomials)))) = table0Tail23Normal
  rw [table0_term92_certificate, table0_term93_certificate, table0_term94_certificate, table0_term95_certificate, table0_tail24_certificate]
  exact table0_tail23_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
