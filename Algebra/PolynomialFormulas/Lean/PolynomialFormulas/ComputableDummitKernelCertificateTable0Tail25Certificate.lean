import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail25Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail25_merge_certificate :
    table0Tail25Candidate = table0Tail25Normal := by
  decide

theorem table0_tail25_certificate :
    SparsePolynomial.substitute table0Tail25 elementaryPolynomials = table0Tail25Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨38, ⟨1, 0, 6, 0, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨5, ⟨1, 0, 5, 2, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-2050, ⟨1, 0, 3, 1, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨780, ⟨1, 0, 2, 3, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail26 elementaryPolynomials)))) = table0Tail25Normal
  rw [table0_term100_certificate, table0_term101_certificate, table0_term102_certificate, table0_term103_certificate, table0_tail26_certificate]
  exact table0_tail25_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
