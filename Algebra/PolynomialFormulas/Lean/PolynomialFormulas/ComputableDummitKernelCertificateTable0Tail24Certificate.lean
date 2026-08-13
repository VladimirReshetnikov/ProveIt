import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail24Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail24_merge_certificate :
    table0Tail24Candidate = table0Tail24Normal := by
  decide

theorem table0_tail24_certificate :
    SparsePolynomial.substitute table0Tail24 elementaryPolynomials = table0Tail24Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-118, ⟨1, 1, 3, 3, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨625, ⟨1, 1, 2, 0, 3⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-850, ⟨1, 1, 1, 2, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨1760, ⟨1, 1, 0, 4, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail25 elementaryPolynomials)))) = table0Tail24Normal
  rw [table0_term96_certificate, table0_term97_certificate, table0_term98_certificate, table0_term99_certificate, table0_tail25_certificate]
  exact table0_tail24_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
