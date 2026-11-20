import Hypotheses
import RHCounterexamples
import StandardReading

namespace RiemannIPRA
open LeanProofs.ConciseIPRA RHCounterexamples

theorem rh_iff_no_counterexample : Prf PRAAx [] (Fm.iff RH (neg (counter RH))) :=
  RHCounterexamples.rh_iff_no_counterexample excess

theorem grh_iff_no_counterexample : Prf PRAAx [] (Fm.iff GRH (neg (counter GRH))) :=
  RHCounterexamples.grh_iff_no_counterexample excess

theorem erh_iff_no_counterexample : Prf PRAAx [] (Fm.iff ERH (neg (counter ERH))) :=
  RHCounterexamples.erh_iff_no_counterexample excess

end RiemannIPRA
