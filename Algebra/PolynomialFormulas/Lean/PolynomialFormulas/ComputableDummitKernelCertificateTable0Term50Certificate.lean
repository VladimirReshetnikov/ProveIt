import PolynomialFormulas.ComputableDummitKernelCertificateTable0Term50Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_term50_certificate :
    SparseTerm.substitute ⟨-700, ⟨3, 1, 3, 0, 2⟩⟩ elementaryPolynomials = table0Term50Normal := by
  decide

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
