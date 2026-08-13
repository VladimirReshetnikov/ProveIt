import PolynomialFormulas.ComputableDummitKernelCertificateTable0Term101Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_term101_certificate :
    SparseTerm.substitute ⟨5, ⟨1, 0, 5, 2, 0⟩⟩ elementaryPolynomials = table0Term101Normal := by
  decide

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
