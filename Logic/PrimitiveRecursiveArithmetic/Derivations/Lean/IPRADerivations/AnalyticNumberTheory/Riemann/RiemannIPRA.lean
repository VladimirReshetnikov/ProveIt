import IPRADerivations.AnalyticNumberTheory.Riemann.CountdownTests
import IPRADerivations.AnalyticNumberTheory.Riemann.PrecisionBounds
import IPRADerivations.AnalyticNumberTheory.Riemann.StripReflection
import IPRADerivations.AnalyticNumberTheory.Riemann.CayleyPackets
import IPRADerivations.AnalyticNumberTheory.Riemann.GridInterpolation
import IPRADerivations.AnalyticNumberTheory.Riemann.HardyToeplitz
import IPRADerivations.AnalyticNumberTheory.Riemann.OneSided
import IPRADerivations.AnalyticNumberTheory.Riemann.ResidueSpace
import IPRADerivations.AnalyticNumberTheory.Riemann.ResidueGram
import IPRADerivations.AnalyticNumberTheory.Riemann.RobinNicolas
import IPRADerivations.AnalyticNumberTheory.Riemann.Hypotheses
import IPRADerivations.AnalyticNumberTheory.Riemann.RHCounterexamples
import IPRADerivations.AnalyticNumberTheory.Riemann.StandardReading
import IPRADerivations.AnalyticNumberTheory.Riemann.ObjectForms
import IPRADerivations.AnalyticNumberTheory.Riemann.SlackForms
import IPRADerivations.AnalyticNumberTheory.Riemann.DiscreteSyntax
import IPRADerivations.AnalyticNumberTheory.Riemann.SparseEvents
import IPRADerivations.AnalyticNumberTheory.Riemann.SplitPrimes
import IPRADerivations.AnalyticNumberTheory.Riemann.PrimeForms
import IPRADerivations.AnalyticNumberTheory.Riemann.MatrixIdentity
import IPRADerivations.AnalyticNumberTheory.Riemann.DivisorMatrices
import IPRADerivations.AnalyticNumberTheory.Riemann.MertensForms
import IPRADerivations.AnalyticNumberTheory.Riemann.MertensSyntax
import IPRADerivations.AnalyticNumberTheory.Riemann.FareyRH
import IPRADerivations.AnalyticNumberTheory.Riemann.FareyEnergy
import IPRADerivations.AnalyticNumberTheory.Riemann.EnergyInequality
import IPRADerivations.AnalyticNumberTheory.Riemann.Lagarias
import IPRADerivations.AnalyticNumberTheory.Riemann.DyadicSeries
import IPRADerivations.AnalyticNumberTheory.Riemann.AbelIdentity
import IPRADerivations.AnalyticNumberTheory.Riemann.ExtraChecks
import IPRADerivations.AnalyticNumberTheory.Riemann.CoefficientTest
import IPRADerivations.AnalyticNumberTheory.Riemann.CubeTests
import IPRADerivations.AnalyticNumberTheory.Riemann.LiouvilleCriterion
import IPRADerivations.AnalyticNumberTheory.Riemann.PowerDivisorBounds
import IPRADerivations.AnalyticNumberTheory.Riemann.PowerDivisorInversion
import IPRADerivations.AnalyticNumberTheory.Riemann.PowerDivisorSyntax
import IPRADerivations.AnalyticNumberTheory.Riemann.ProductCertificate
import IPRADerivations.AnalyticNumberTheory.Riemann.SymmetricPrefixes
import IPRADerivations.AnalyticNumberTheory.Riemann.TaylorPackets
import IPRADerivations.AnalyticNumberTheory.Riemann.UniversalCriteria

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
