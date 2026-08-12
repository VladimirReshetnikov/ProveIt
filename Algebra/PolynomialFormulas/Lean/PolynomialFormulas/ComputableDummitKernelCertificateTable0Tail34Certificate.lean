import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail34Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail34_merge_certificate :
    table0Tail34Candidate = table0Tail34Normal := by
  decide

theorem table0_tail34_certificate :
    SparsePolynomial.substitute table0Tail34 elementaryPolynomials = table0Tail34Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨256, ⟨0, 0, 0, 6, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-9375, ⟨0, 0, 0, 1, 4⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail35 elementaryPolynomials)) = table0Tail34Normal
  rw [table0_term136_certificate, table0_term137_certificate, table0_tail35_certificate]
  exact table0_tail34_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
