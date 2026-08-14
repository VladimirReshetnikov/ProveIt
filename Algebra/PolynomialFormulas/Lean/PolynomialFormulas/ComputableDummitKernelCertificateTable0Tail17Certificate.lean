import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail17Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail17_merge_certificate :
    table0Tail17Candidate = table0Tail17Normal := by
  decide

theorem table0_tail17_certificate :
    SparsePolynomial.substitute table0Tail17 elementaryPolynomials = table0Tail17Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨19, ⟨2, 2, 2, 3, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-125, ⟨2, 2, 1, 0, 3⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-610, ⟨2, 2, 0, 2, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-36, ⟨2, 1, 5, 0, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail18 elementaryPolynomials)))) = table0Tail17Normal
  rw [table0_term68_certificate, table0_term69_certificate, table0_term70_certificate, table0_term71_certificate, table0_tail18_certificate]
  exact table0_tail17_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
