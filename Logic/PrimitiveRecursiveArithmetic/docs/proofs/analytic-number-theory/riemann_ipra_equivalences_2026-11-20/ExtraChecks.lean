import DyadicSeries
import FareyEnergy
import SmokePR

/-! Small evaluations of the actual ProveIt PR trees. -/
namespace ExtraChecks
open RiemannIPRA.Smoke
#guard vecEval Lagarias.divisorSum #v[4] == 7
#guard vecEval Lagarias.harmonicNumerator #v[3] == 11
#guard vecEval (DivisorMatrices.leibnizPart false false) #v[1,0,0,1,1,0,2] == 1
#guard vecEval (DivisorMatrices.leibnizPart false true) #v[1,0,0,1,1,0,2] == 1
#guard vecEval FareyEnergy.jordanTwo #v[2] == 3
#guard vecEval DyadicSeries.denominator #v[1,4] == 4
end ExtraChecks
