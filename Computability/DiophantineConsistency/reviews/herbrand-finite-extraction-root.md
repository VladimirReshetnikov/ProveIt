# Independent replay: finite Herbrand extraction for prepared sequents

For a cut-free prepared existential sequent with an open target matrix and a
finite list of actual universal-theory axioms, Lean proves that the universal
theory derives the universally closed finite disjunction of target instances
at the existential-rule terms appearing in the derivation. It first proves
soundness of a finite-term interpretation for cut-free proofs without
universal-rule nodes, then relates that interpretation to ordinary truth and
eliminates the negated axiom alternatives. The proof applies to every free
variable valuation.

This result does not yet turn a general ∀∃ proof into the required prepared
sequent, ensure collected terms use only the intended parameters, translate
them to primitive-recursive witness codes, or prove PRA conservation. The
separate selector handles the later finite-disjunction-to-witness step when
its own hypotheses are supplied.

Two isolated builds against the independently refreshed 17-module provider
`/tmp/pra-parameter-independent-ls8rb3lm/lib` passed all ten modules and
checks with identical source, object and complete-log hashes, without
warnings or `sorryAx`. The driver verifies frozen parent sources and objects.
[Independent driver, state and logs](herbrand-finite-extraction-root-replay/)
and the [author packet](herbrand-finite-extraction-author-replay/) are
preserved. Historical failed probes are evidence only; Foundation, Mathlib
and unchanged local objects remain inherited cache boundaries.
