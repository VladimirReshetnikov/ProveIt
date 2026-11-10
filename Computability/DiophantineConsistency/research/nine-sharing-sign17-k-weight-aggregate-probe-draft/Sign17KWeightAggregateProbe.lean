import DiophantineConsistency.Sign17ExactDegree

/-! SOURCE-ONLY: one uniformly quantified K weight batch, not a rank theorem. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign17KWeightAggregateProbe
open WangTiles942

def indices : Fin 32 → Fin 942 := ![0, 926, 925, 924, 923, 941, 938, 935, 940, 937, 934, 939, 936, 933, 932, 931, 930, 432, 832, 431, 831, 830, 829, 828, 827, 826, 825, 824, 823, 822, 821, 922]
def weights : Fin 32 → ℕ := ![34876427265, 15049678914561, 15049678652417, 15049565668353, 15049565406209, 15015588664321, 15015588661249, 15015588660225, 15015454446593, 15015454443521, 15015454442497, 15015320228865, 15015320225793, 15015320224769, 14981094967297, 14946735228929, 14912375490561, 14877880222721, 14877767185409, 14843520222209, 14843407184897, 14809047707649, 14774687707137, 14740328229889, 14705968229377, 14671608752129, 14637248751617, 14602889274369, 14568529273857, 14534169796609, 14499809796097, 14498870330369]

theorem all_weights (i : Fin 32) : selectorWeight (tile (indices i)) = weights i := by
  fin_cases i <;> decide +kernel

end DiophantineConsistency.Sign17KWeightAggregateProbe
#print axioms DiophantineConsistency.Sign17KWeightAggregateProbe.all_weights
