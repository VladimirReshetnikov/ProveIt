# Independent exact 2011 DAG iPRA client audit

The read-only [audit](audit.py) of `652071b812` actually exited 0 in session
2072; its [receipt](CHECK.json) and [terminal observation](terminal-observation.json)
record both matched source/object chains, exact direct imports, recorded
child and outer exits, six named axiom reports per side, and a successful
rerun of the full independently audited 684-row parent chain. Each report
lists Lean metatheory `propext`, `Classical.choice`, and `Quot.sound`, with
no warnings or `sorryAx`. No Lean compilation was rerun for this review.

The checked `standard_translated_consistencyDag` states Lean derivability in
the selected standard iPRA presentation of an equivalence between
`nativeNoZero Thirteen69Cuts.currentLiteral` and the Gödel–Gentzen image of
Foundation's selected ZFC consistency sentence after the stated language
embedding. `currentLiteral` is `positiveShift (literal
CurrentWindowCarry2011.ports)`, with the fixed 2011 tuple. The native and
reference theorems use the separately stated mapped native refutation and
order-erased encodings. The other two checked declarations transfer the
model-level same-no-zero fact to the polynomial bridge; all six exact names
and their axiom sets were checked.

The 69-operation count describes the shared arithmetic DAG on positive
coordinates. The theorem uses its positive shift to quantify over unrestricted
model naturals; it does not claim the unshared expanded shifted syntax has
69 operations. The selected 2011 ports differ from phase-split2471. This
proves existence of derivations in the specified Lean formalizations; it
does not display a literal proof, establish global equation minimality, or
identify a different consistency coding or fixed tuple solely by name.

The client's opening source comment calling it uncompiled is stale: the
paired evidence checked here records successful compilation. The inherited
Foundation outer-wrapper exit remains unobserved; package-transitive/dynamic
ancestry and mutations between checks remain outside this review. Later
upstream files added in `ec42d7f83b` and `6f8dd13085` were outside the frozen
parent replay.
