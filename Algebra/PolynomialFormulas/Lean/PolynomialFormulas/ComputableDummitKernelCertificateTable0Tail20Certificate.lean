import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail20Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail20_merge_certificate :
    table0Tail20Candidate = table0Tail20Normal := by
  decide

theorem table0_tail20_certificate :
    SparsePolynomial.substitute table0Tail20 elementaryPolynomials = table0Tail20Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-3500, ⟨2, 0, 1, 1, 3⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-1450, ⟨2, 0, 0, 3, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨198, ⟨1, 5, 1, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-78, ⟨1, 5, 0, 2, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail21 elementaryPolynomials)))) = table0Tail20Normal
  rw [table0_term80_certificate, table0_term81_certificate, table0_term82_certificate, table0_term83_certificate, table0_tail21_certificate]
  exact table0_tail20_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
