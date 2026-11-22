import IPRADerivations.AnalyticNumberTheory.Riemann.DyadicSeries
import IPRADerivations.AnalyticNumberTheory.Riemann.FareyEnergy
import IPRADerivations.AnalyticNumberTheory.Riemann.SmokePR

/-! Imported from the packet `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`,
`ExtraChecks.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Small evaluations of the actual ProveIt PR trees. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.ExtraChecks
open RiemannIPRA.Smoke
#guard vecEval Lagarias.divisorSum #v[4] == 7
#guard vecEval Lagarias.harmonicNumerator #v[3] == 11
#guard vecEval (DivisorMatrices.leibnizPart false false) #v[1,0,0,1,1,0,2] == 1
#guard vecEval (DivisorMatrices.leibnizPart false true) #v[1,0,0,1,1,0,2] == 1
#guard vecEval FareyEnergy.jordanTwo #v[2] == 3
#guard vecEval DyadicSeries.denominator #v[1,4] == 4
end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.ExtraChecks
