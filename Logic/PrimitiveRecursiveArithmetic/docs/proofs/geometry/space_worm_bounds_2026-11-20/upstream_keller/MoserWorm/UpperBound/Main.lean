import MoserWorm.Common.Audit
import MoserWorm.UpperBound.Certificate.GeometricSound
import MoserWorm.UpperBound.Certificate.Generated.Assembly

/-! The concrete upper bound, instantiated with the kernel-checked certificate. -/

open MeasureTheory

namespace MoserWorm

open UpperBound UpperBound.Certificate

theorem upper_bound :
    IsConvexUniversalCover Kquad ∧
      volume Kquad = ENNReal.ofReal (areaK : ℝ) :=
  checkCert_upper_bound Generated.theCert Generated.certOK

theorem optimalArea_upper_bound :
    optimalArea ≤ ENNReal.ofReal (areaK : ℝ) :=
  checkCert_optimalArea_upper_bound Generated.theCert Generated.certOK

end MoserWorm

audit_axioms MoserWorm.upper_bound MoserWorm.optimalArea_upper_bound
