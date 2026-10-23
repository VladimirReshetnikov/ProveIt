import DiophantineConsistency.SplitCircuitRegisters59
open DiophantineConsistency.SplitCircuitRegisters59
#print axioms natural_baseRegister
#print axioms natural_kernel0Register
#print axioms natural_kernel1Register
#print axioms natural_kernel2Register
#print axioms natural_ellRegister
#print axioms natural_targetsRegister
#print axioms natural_thresholdRegister
#print axioms natural_marginScaleRegister
#print axioms natural_sourceHighRegister
#print axioms natural_sourceSRegister
#print axioms natural_sourceTRegister
#print axioms natural_blockLengthRegister
#print axioms natural_sourceRankRegister

-- The whole tuple is bound coherently to its ten coefficient and two scale recipes.
example {R : Type*} [CommRing R] (ports : Fin 4 → R) (height scale : R) :
    fixedLeaves ports height scale 4 = 2*ports 0+2*ports 0*ports 1 := rfl
