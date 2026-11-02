# Same-language standard-iPRA AQ29 client: uncompiled draft

[`IPRAStandardTheory.standardTheory`](../../Lean/DiophantineConsistency/IPRAStandardTheory.lean)
uses the same full primitive-recursive code language as `nativeTheory`, with
atomic Leibniz replacement instead of full formula replacement and
successor-step quantifier-free induction instead of the `x + 1` step. It
shares the candidate theory's defining equations, successor basic axioms and
definition of `<`. Its source states the same-language theorem
`provable_iff`: both theories derive exactly the same sentences. This does not
itself compare the separate equality-only reference language, and no coherent
replay of the newly merged source has been recorded here.

The [AQ29 client](draft/IPRAStandardAQ29.lean) is a **draft, not yet compiled**.
It applies `provable_iff` to the native AQ29 endpoint and to the existing
Foundation consistency comparison, and states their composition in
`standardTheory`. The latter uses the Gödel–Gentzen translation of the mapped
Foundation consistency sentence and the selected Foundation proof coding; it
does not claim identification with arbitrary alternate proof codings. The
[checks draft](draft/IPRAStandardAQ29Checks.lean) requests axiom reports for the
comparison and three client declarations. These files and all their required
sources must be elaborated and independently replayed on a coherent provider
before they can establish a result.

The [provisional survey](survey-receipt.json), made with the existing
line-based planner against the in-progress AQ29 parent's pinned source
manifest, reports 1,209 parent modules and six additions: successor induction,
general addition-one, its converse, `IPRAStandardTheory`, and the two client
drafts. It found no new direct external imports. The two drafts were untracked
when surveyed. **Parent bytes and source drift were not checked**; the scan is
not Lean's dependency parser. The survey records neither a parent build pass
nor evidence that any addition compiles.

After the existing two-run parent completes, a credible extension needs the
actual observed successful coordinator exit and parent comparator checks, a
strict source audit and authenticated snapshot of all six additions, an exact
checks policy, isolated sibling inputs and two completed Lean replays. The
existing [reference extension tools](../reference-coherent-replay/extension/)
use a reference-specific hard-coded target policy and cannot be applied to
this standard client without a separately reviewed policy adaptation. The
in-progress parent already has known workspace source drift, so a result from
it would be historical unless a coherent successor is rebuilt. Package-
transitive and dynamic provenance, and the parent Foundation wrapper's
unobserved outer exit, retain their documented limits.
