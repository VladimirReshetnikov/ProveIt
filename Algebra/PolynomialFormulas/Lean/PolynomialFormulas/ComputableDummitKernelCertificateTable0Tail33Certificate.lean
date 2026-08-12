import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail33Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail33_merge_certificate :
    table0Tail33Candidate = table0Tail33Normal := by
  decide

theorem table0_tail33_certificate :
    SparsePolynomial.substitute table0Tail33 elementaryPolynomials = table0Tail33Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-124, ⟨0, 0, 5, 1, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨17, ⟨0, 0, 4, 3, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨3250, ⟨0, 0, 2, 2, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-1600, ⟨0, 0, 1, 4, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail34 elementaryPolynomials)))) = table0Tail33Normal
  rw [table0_term132_certificate, table0_term133_certificate, table0_term134_certificate, table0_term135_certificate, table0_tail34_certificate]
  exact table0_tail33_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
