import IPRAComplexity

-- Print the kernel dependencies of every theorem in the checked core.
#print axioms IPRAComplexity.bany_correct
#print axioms IPRAComplexity.ball_correct
#print axioms IPRAComplexity.bany_false_iff
#print axioms IPRAComplexity.firstWitness_sound
#print axioms IPRAComplexity.firstWitness_none_iff
#print axioms IPRAComplexity.bany_has_witness
#print axioms IPRAComplexity.iterate_add
#print axioms IPRAComplexity.iterate_fixed
#print axioms IPRAComplexity.Machine.acceptWithin_add
#print axioms IPRAComplexity.Machine.acceptWithin_mono
#print axioms IPRAComplexity.trace_unique
#print axioms IPRAComplexity.Polynomial.eval_subst
#print axioms IPRAComplexity.Polynomial.eval_mono
#print axioms IPRAComplexity.Walk.append
#print axioms IPRAComplexity.Walk.split
#print axioms IPRAComplexity.Walk.map
#print axioms IPRAComplexity.Walk.stay
#print axioms IPRAComplexity.Walk.source_bound
#print axioms IPRAComplexity.Walk.target_bound
#print axioms IPRAComplexity.Walk.erase_stutters
#print axioms IPRAComplexity.reach_correct
#print axioms IPRAComplexity.reach_iff_short_walk
#print axioms IPRAComplexity.andClauses_correct
#print axioms IPRAComplexity.notClauses_correct
#print axioms IPRAComplexity.constClauses_correct
#print axioms IPRAComplexity.CNF.eval_append
#print axioms IPRAComplexity.Gate.clauses_correct
#print axioms IPRAComplexity.GateSystem.clauses_correct
#print axioms IPRAComplexity.Gate.clauses_width
#print axioms IPRAComplexity.Gate.clauses_count
#print axioms IPRAComplexity.GateSystem.clauses_count

-- Audit proof-bearing definitions as well.
#print axioms IPRAComplexity.Reduction.id
#print axioms IPRAComplexity.Reduction.comp
#print axioms IPRAComplexity.PolyMap.comp
#print axioms IPRAComplexity.PolyCost.comp
#print axioms IPRAComplexity.PolyReduction.comp
#print axioms IPRAComplexity.countdown
