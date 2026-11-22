import CountdownTests
import PrecisionBounds
import StripReflection
import CayleyPackets
import GridInterpolation
import HardyToeplitz
import OneSided
import ResidueSpace
import ResidueGram
import RobinNicolas
import Hypotheses
import RHCounterexamples
import StandardReading
import ObjectForms
import SlackForms
import DiscreteSyntax
import SparseEvents
import SplitPrimes
import PrimeForms
import MatrixIdentity
import DivisorMatrices
import MertensForms
import MertensSyntax
import FareyRH
import FareyEnergy
import EnergyInequality
import Lagarias
import DyadicSeries
import AbelIdentity
import ExtraChecks
import CoefficientTest
import CubeTests
import LiouvilleCriterion
import PowerDivisorBounds
import PowerDivisorInversion
import PowerDivisorSyntax
import ProductCertificate
import SymmetricPrefixes
import TaylorPackets
import UniversalCriteria

namespace RiemannIPRA
open LeanProofs.ConciseIPRA RHCounterexamples

theorem rh_iff_no_counterexample : Prf PRAAx [] (Fm.iff RH (neg (counter RH))) :=
  RHCounterexamples.rh_iff_no_counterexample excess

theorem grh_iff_no_counterexample : Prf PRAAx [] (Fm.iff GRH (neg (counter GRH))) :=
  RHCounterexamples.grh_iff_no_counterexample excess

theorem erh_iff_no_counterexample : Prf PRAAx [] (Fm.iff ERH (neg (counter ERH))) :=
  RHCounterexamples.erh_iff_no_counterexample excess

end RiemannIPRA
