import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail31Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail31_merge_certificate :
    table0Tail31Candidate = table0Tail31Normal := by
  decide

theorem table0_tail31_certificate :
    SparsePolynomial.substitute table0Tail31 elementaryPolynomials = table0Tail31Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨3125, ⟨0, 2, 0, 0, 4⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-13, ⟨0, 1, 6, 1, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-125, ⟨0, 1, 4, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨590, ⟨0, 1, 3, 2, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail32 elementaryPolynomials)))) = table0Tail31Normal
  rw [table0_term124_certificate, table0_term125_certificate, table0_term126_certificate, table0_term127_certificate, table0_tail32_certificate]
  exact table0_tail31_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
