import PolynomialFormulas.ComputableDummitKernelCertificateTable0Term100Data

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 20000000 in
theorem table0_term100_certificate :
    SparseTerm.substitute ⟨38, ⟨1, 0, 6, 0, 1⟩⟩ elementaryPolynomials = table0Term100Normal := by
  decide

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
