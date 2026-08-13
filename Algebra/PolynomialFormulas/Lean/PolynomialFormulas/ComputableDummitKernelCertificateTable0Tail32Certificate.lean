import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail32Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail32_merge_certificate :
    table0Tail32Candidate = table0Tail32Normal := by
  decide

theorem table0_tail32_certificate :
    SparsePolynomial.substitute table0Tail32 elementaryPolynomials = table0Tail32Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-16, ⟨0, 1, 2, 4, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-1250, ⟨0, 1, 1, 1, 3⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-2000, ⟨0, 1, 0, 3, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨1, ⟨0, 0, 8, 0, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail33 elementaryPolynomials)))) = table0Tail32Normal
  rw [table0_term128_certificate, table0_term129_certificate, table0_term130_certificate, table0_term131_certificate, table0_tail33_certificate]
  exact table0_tail32_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
