# Sign24 full coefficient and lower bound: author pass

The author observed outer session `61892` exit **0**. All seven stages compiled
with child exit 0 and the runner completed its final postflight. The checked
chain establishes that the actual sign24 seed evaluated on its axis has eighth
coefficient one, identifies it with the diagonal specialization of the actual
direct Fin24 expression, and proves
`8 ≤ (Sign24AbstractExpression.expression p).toPolynomial.totalDegree` for
every `p : Fin 4 → ℤ`. Reports list `[propext, Classical.choice, Quot.sound]`
or subsets, with no `sorryAx`. The seed coefficient stage retains one unused
`Function.comp_apply` simp-argument warning.

This lower bound passed an [independent terminal audit](../../../reviews/nine-sharing-sign24-full-coeff-retry02-terminal-independent/README.md).
Combining it with the separately checked upper bound requires another client.
The source headers say `SOURCE-ONLY`; the exact snapshot's status is
superseded by the checked run. The
finite checks retain their scoped 4,000,000 heartbeat settings; sampled RSS
and point-time provider observations do not establish full dynamic or
transitive ancestry. No external JSON/port-byte or PDF binding follows.
Copied state and logs are retained here, and `outer-result.json` separately
records numeric outer exit.
