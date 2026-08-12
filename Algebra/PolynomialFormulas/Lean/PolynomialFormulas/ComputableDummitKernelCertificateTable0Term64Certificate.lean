import PolynomialFormulas.ComputableDummitKernelCertificateTable0Term64Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_term64_certificate :
    SparseTerm.substitute ⟨-185, ⟨2, 3, 2, 0, 2⟩⟩ elementaryPolynomials = table0Term64Normal := by
  decide

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
