import IPRADerivations.AnalyticNumberTheory.Riemann.PrecisionBounds
import IPRADerivations.AnalyticNumberTheory.Riemann.StripReflection
import IPRADerivations.AnalyticNumberTheory.Riemann.CayleyPackets
import IPRADerivations.AnalyticNumberTheory.Riemann.HardyToeplitz
import IPRADerivations.AnalyticNumberTheory.Riemann.OneSided
import IPRADerivations.AnalyticNumberTheory.Riemann.ResidueGram
import IPRADerivations.AnalyticNumberTheory.Riemann.RobinNicolas
import IPRADerivations.AnalyticNumberTheory.Riemann.SlackForms
import IPRADerivations.AnalyticNumberTheory.Riemann.SparseEvents
import IPRADerivations.AnalyticNumberTheory.Riemann.MatrixIdentity
import IPRADerivations.AnalyticNumberTheory.Riemann.MertensForms
import IPRADerivations.AnalyticNumberTheory.Riemann.FareyRH
import IPRADerivations.AnalyticNumberTheory.Riemann.AbelIdentity
import IPRADerivations.AnalyticNumberTheory.Riemann.ExtraChecks
import IPRADerivations.AnalyticNumberTheory.Riemann.CoefficientTest
import IPRADerivations.AnalyticNumberTheory.Riemann.LiouvilleCriterion
import IPRADerivations.AnalyticNumberTheory.Riemann.PowerDivisorSyntax
import IPRADerivations.AnalyticNumberTheory.Riemann.ProductCertificate

/-! Imported from the packet `analytic-number-theory/riemann_ipra_formalization_2026-11-20`,
`RiemannIPRA.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA
open LeanProofs.ConciseIPRA RHCounterexamples

theorem rh_iff_no_counterexample : Prf PRAAx [] (Fm.iff RH (neg (counter RH))) :=
  RHCounterexamples.rh_iff_no_counterexample excess

theorem grh_iff_no_counterexample : Prf PRAAx [] (Fm.iff GRH (neg (counter GRH))) :=
  RHCounterexamples.grh_iff_no_counterexample excess

theorem erh_iff_no_counterexample : Prf PRAAx [] (Fm.iff ERH (neg (counter ERH))) :=
  RHCounterexamples.erh_iff_no_counterexample excess

end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.RiemannIPRA
