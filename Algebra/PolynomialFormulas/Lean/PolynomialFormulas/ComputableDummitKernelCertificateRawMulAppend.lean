import PolynomialFormulas.ComputableDummitCoefficientsCore

namespace LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate

open LeanProofs.PolynomialFormulas.ComputableDummitCoefficients

set_option maxRecDepth 1000000

set_option maxHeartbeats 20000000

theorem rawMul_append_certificate (p r q : SparsePolynomial) :
    SparsePolynomial.rawMul (p ++ r) q =
      SparsePolynomial.rawMul p q ++ SparsePolynomial.rawMul r q := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      change q.map (SparseTerm.mul t) ++
          SparsePolynomial.rawMul (p ++ r) q =
        (q.map (SparseTerm.mul t) ++ SparsePolynomial.rawMul p q) ++
          SparsePolynomial.rawMul r q
      rw [ih, List.append_assoc]

end LeanProofs.PolynomialFormulas.ComputableDummitCoefficients.KernelCertificate
