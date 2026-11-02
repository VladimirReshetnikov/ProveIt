# Fourteen-variable standard-iPRA author-extension plan

Upstream's [`IPRAStandardCurrentEndpoint.lean`](../../Lean/DiophantineConsistency/IPRAStandardCurrentEndpoint.lean)
states in the same-language `standardTheory` both the 14-variable no-zero
equivalence with the native negation of the selected Foundation refutation
predicate and its equivalence with the Gödel–Gentzen image of Foundation's
selected consistency sentence. The upstream commit reports an ordinary Lake
author build; that report is not an independent replay packet. The standard
and native theories share their primitive-recursive defining and basic axiom
schemes, including defined `<`; this is not the separate equality-only
translation.

`author-plan.py` plans an additional single-author historical-hybrid
compilation against the independently audited fresh AQ29 author parent. It
pins the exact parent manifest and tracked Git source bytes, reports the
source-declared parent/addition graph and its direct external difference, and
records the four exact diagnostics. The scan uses a source-line import parser,
not Lean dependency discovery; it does not rehash or authenticate the parent,
establish that a module compiles, prove the endpoint, or claim a paired or
current-source result. The actual author-only driver would recheck Lean's
direct dependencies and all guarded parent inputs before and after a run.

The frozen parent differs from today's workspace in `NaturalExpression.lean`
and other sources. Consequently, even a successful author-only extension would
be a historical hybrid and would not automatically identify its 14-variable
literal with the current PDF. Package-transitive and dynamic ancestry remain
inherited, and the Foundation builder's outer exit was not observed.
