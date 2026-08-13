import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail28Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail28_merge_certificate :
    table0Tail28Candidate = table0Tail28Normal := by
  decide

theorem table0_tail28_certificate :
    SparsePolynomial.substitute table0Tail28 elementaryPolynomials = table0Tail28Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-99, ⟨0, 5, 0, 1, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-150, ⟨0, 4, 2, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨196, ⟨0, 4, 1, 2, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨48, ⟨0, 4, 0, 4, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail29 elementaryPolynomials)))) = table0Tail28Normal
  rw [table0_term112_certificate, table0_term113_certificate, table0_term114_certificate, table0_term115_certificate, table0_tail29_certificate]
  exact table0_tail28_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
