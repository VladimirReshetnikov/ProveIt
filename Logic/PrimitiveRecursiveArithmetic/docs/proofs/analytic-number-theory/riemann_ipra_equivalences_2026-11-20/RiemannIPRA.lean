import Hypotheses
import RHCounterexamples
import StandardReading
import ObjectForms
import SlackForms
import DiscreteSyntax
import SparseEvents
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

namespace RiemannIPRA
open LeanProofs.ConciseIPRA RHCounterexamples

theorem rh_iff_no_counterexample : Prf PRAAx [] (Fm.iff RH (neg (counter RH))) :=
  RHCounterexamples.rh_iff_no_counterexample excess

theorem grh_iff_no_counterexample : Prf PRAAx [] (Fm.iff GRH (neg (counter GRH))) :=
  RHCounterexamples.grh_iff_no_counterexample excess

theorem erh_iff_no_counterexample : Prf PRAAx [] (Fm.iff ERH (neg (counter ERH))) :=
  RHCounterexamples.erh_iff_no_counterexample excess

end RiemannIPRA
