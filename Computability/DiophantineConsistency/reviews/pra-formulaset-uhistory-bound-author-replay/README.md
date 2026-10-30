# Formula-set syntax with bounded UFormula histories

This client composes the exact Foundation arity-zero `isSemiformula` and `isUFormula` fixpoint syntax into the positive formula-set bound. For every relevant index, the theorem assumes a sequence code below the common bound, a bit-membership witness, and a separately bounded actual `limSeqDef`; a bounded BV graph remains a separate hypothesis. No uniform history majorant or rho/HA certificate is supplied. The sentence is proved in candidate PRA by IOpen model reasoning and completeness.

Replay: `python3 Computability/DiophantineConsistency/reviews/pra-formulaset-uhistory-bound-author-replay/replay.py --parent /tmp/pra-fixbit-uformula-independent-5xao74nr/lib`. Parent is the independently replayed isUFormula client on the independently replayed 20-module graph; the Foundation transitive graph is inherited with listed source/object anchors checked.
