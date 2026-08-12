import PolynomialFormulas.ComputableDummitKernelCertificateTable0Term80Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_term80_certificate :
    SparseTerm.substitute ⟨-3500, ⟨2, 0, 1, 1, 3⟩⟩ elementaryPolynomials = table0Term80Normal := by
  decide

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
