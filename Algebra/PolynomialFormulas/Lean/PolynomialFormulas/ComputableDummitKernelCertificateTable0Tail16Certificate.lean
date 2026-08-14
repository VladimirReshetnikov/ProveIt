import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail16Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail16_merge_certificate :
    table0Tail16Candidate = table0Tail16Normal := by
  decide

theorem table0_tail16_certificate :
    SparsePolynomial.substitute table0Tail16 elementaryPolynomials = table0Tail16Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-185, ⟨2, 3, 2, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨168, ⟨2, 3, 1, 2, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-128, ⟨2, 3, 0, 4, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨93, ⟨2, 2, 3, 1, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail17 elementaryPolynomials)))) = table0Tail16Normal
  rw [table0_term64_certificate, table0_term65_certificate, table0_term66_certificate, table0_term67_certificate, table0_tail17_certificate]
  exact table0_tail16_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
