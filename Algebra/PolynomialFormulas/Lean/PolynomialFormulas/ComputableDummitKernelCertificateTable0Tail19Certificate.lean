import PolynomialFormulas.ComputableDummitKernelCertificateTable0Tail19Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_tail19_merge_certificate :
    table0Tail19Candidate = table0Tail19Normal := by
  decide

theorem table0_tail19_certificate :
    SparsePolynomial.substitute table0Tail19 elementaryPolynomials = table0Tail19Normal := by
  change SparsePolynomial.add (SparseTerm.substitute ⟨-3125, ⟨2, 1, 0, 0, 4⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨375, ⟨2, 0, 4, 0, 2⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨-172, ⟨2, 0, 3, 2, 1⟩⟩ elementaryPolynomials) (SparsePolynomial.add (SparseTerm.substitute ⟨82, ⟨2, 0, 2, 4, 0⟩⟩ elementaryPolynomials) (SparsePolynomial.substitute table0Tail20 elementaryPolynomials)))) = table0Tail19Normal
  rw [table0_term76_certificate, table0_term77_certificate, table0_term78_certificate, table0_term79_certificate, table0_tail20_certificate]
  exact table0_tail19_merge_certificate

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
