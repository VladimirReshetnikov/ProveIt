import PolynomialFormulas.ComputableDummitKernelCertificateTable0Term128Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_term128_certificate :
    SparseTerm.substitute ⟨-16, ⟨0, 1, 2, 4, 0⟩⟩ elementaryPolynomials = table0Term128Normal := by
  decide

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
