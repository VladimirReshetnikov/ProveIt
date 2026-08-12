import PolynomialFormulas.ComputableDummitCoefficientsCore

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

theorem flattenBuckets_append_certificate (p r : List SparsePolynomial) :
    SparsePolynomial.flattenBuckets (p ++ r) =
      SparsePolynomial.flattenBuckets p ++
        SparsePolynomial.flattenBuckets r := by
  induction p with
  | nil => rfl
  | cons b p ih =>
      change b ++ SparsePolynomial.flattenBuckets (p ++ r) =
        (b ++ SparsePolynomial.flattenBuckets p) ++
          SparsePolynomial.flattenBuckets r
      rw [ih, List.append_assoc]

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
