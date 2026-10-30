# BV graph and explicit pair polynomial

The arity-zero semiformula path needs the Foundation graph `bvGraph L` at value zero. This graph is the rewritten result of `BV.blueprint L`, which in turn uses an intermediate `UformulaRec1` graph and a recursively defined fixpoint.

`PRABVRecGraphBound` proves in candidate PRA a bound for that exact intermediate graph, given a pair code, its size bound, and a bounded graph for the BV blueprint fixpoint. The proof handles the actual `pair₃Def` subformula with its local witness bound `pr+1`. `PRABVGraphZeroBound` then binds the intermediate graph into the actual zero-valued `bvGraph L`; its closed candidate-PRA sentence retains the pair-code and bounded-fixpoint hypotheses.

`PRABVPairPolynomial` discharges one of those concrete witness constructions: Foundation's exact pair code for `(0,p,0)` is `(p*p+p)^2`. It proves both that equality in every IOpen model and a closed candidate-PRA sentence asserting the actual `pair₃Def` graph at that polynomial. No assumption of a supplied pair witness appears in that sentence.

These results do not supply a uniform bound for the BV recursive fixpoint history. They do not yet establish a complete ZFC refutation witness bound or an HA proof. Reproducible builds and the exact inherited Foundation scope are recorded in the corresponding `pra-bv-rec-graph-bound-author-replay`, `pra-bv-graph-zero-bound-author-replay`, and `pra-bv-pair-polynomial-author-replay` review packets.
