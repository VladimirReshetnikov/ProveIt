import ObjectTargets
import LexFuel
import RationalRoots
import EliminationTargets

#print axioms LeanProofs.ConciseIPRA.TermCompiler.symbol_correct
#print axioms LeanProofs.ConciseIPRA.TermCompiler.transport_equation
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.denote_compiled
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.compiled_zero
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.compiled_succ
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.object_backward_zero
#print axioms LeanProofs.ConciseIPRA.DemandCompiler.object_backward_succ
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_iterateSymbol
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_fuelSymbol
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_fuelParamSymbol
#print axioms LeanProofs.ConciseIPRA.LexFuel.denote_boundSymbol

-- None of the printed lists may contain sorryAx or Classical.choice.
-- propext and Quot.sound are host-kernel dependencies, not iPRA axioms.
