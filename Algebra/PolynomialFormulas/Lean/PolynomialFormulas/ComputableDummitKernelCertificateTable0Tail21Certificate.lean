import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail21Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail21_merge_certificate :
    table0Tail21Candidate = table0Tail21Normal := by
  decide

theorem table0_tail21_certificate :
    SparsePolynomial.substitute table0Tail21 elementaryPolynomials = table0Tail21Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-95, ⟨1, 4, 2, 1, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨44, ⟨1, 4, 1, 3, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨25, ⟨1, 3, 4, 0, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-15, ⟨1, 3, 3, 2, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail22 elementaryPolynomials)))) = table0Tail21Normal
  rw [table0_term84_certificate, table0_term85_certificate, table0_term86_certificate, table0_term87_certificate, table0_tail22_certificate]
  exact table0_tail21_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
