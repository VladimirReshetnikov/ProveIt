# Same-language standard-iPRA AQ29 client

**Promoted (3 November 2026).** The Lean files of this directory were copied byte for byte into `Lean/DiophantineConsistency/` and built there against current sources; see the [promotion record](../../reviews/aq22-28-current-source-promotion/README.md). The tree copies are now canonical; the copies here are retained as the audited historical inputs.

[`IPRAStandardTheory.standardTheory`](../../Lean/DiophantineConsistency/IPRAStandardTheory.lean)
uses the same full primitive-recursive code language as `nativeTheory`, with
atomic Leibniz replacement instead of full formula replacement and
successor-step quantifier-free induction instead of the `x + 1` step. It
shares the candidate theory's defining equations, successor basic axioms and
definition of `<`. Its source states the same-language theorem
`provable_iff`: both theories derive exactly the same sentences. This does not
itself compare the separate equality-only reference language.

The [AQ29 client](draft/IPRAStandardAQ29.lean) has completed one guarded
author-only extension over the fresh AQ29 author provider. Its [trial packet](../../reviews/ipra-standard-aq29-author-trial/README.md)
records an observed process exit 0 and all six compiled additions; an
[independent artifact audit](../../reviews/ipra-standard-aq29-author-independent-audit/README.md)
also exited 0. This is a historical hybrid, not a matched peer or current-source
result; its parent has 15 recorded source drifts. Package-transitive and dynamic
ancestry remain inherited, and the Foundation build wrapper's outer exit was
not observed.

It applies `provable_iff` to the native AQ29 endpoint and to the existing
Foundation consistency comparison, and states their composition in
`standardTheory`. The latter uses the Gödel–Gentzen translation of the mapped
Foundation consistency sentence and the selected Foundation proof coding; it
does not claim identification with arbitrary alternate proof codings. The
[checks source](draft/IPRAStandardAQ29Checks.lean) requests axiom reports for the
comparison and three client declarations. An independent Lean replay and the
matched parent pair remain outstanding.

The [provisional survey](survey-receipt.json), made with the existing
line-based planner against the in-progress AQ29 parent's pinned source
manifest, reports 1,209 parent modules and six additions: successor induction,
general addition-one, its converse, `IPRAStandardTheory`, and the two client
drafts. It found no new direct external imports. All six additions were tracked
and unmodified at the observed Git head. **Parent bytes and source drift were not checked**; the scan is
not Lean's dependency parser. The survey itself predates the author pass and
does not establish that result.

After the existing two-run parent completes, a credible extension needs the
actual observed successful coordinator exit and parent comparator checks, a
strict source audit and authenticated snapshot of all six additions, an exact
checks policy, isolated sibling inputs and two completed Lean replays. The
existing [reference extension tools](../reference-coherent-replay/extension/)
use a reference-specific target policy. A separate [dedicated adaptation](extension/README.md)
has passed toy controls but still needs independent review. The
in-progress parent already has known workspace source drift. The dedicated
freezer requires a strict current-source plan, so it cannot use that parent
directly while the drift remains. A separate [historical-parent workflow](historical/README.md)
has passed independently rerun toy controls and source review; it cannot yield
a current-source claim. Package-
transitive and dynamic provenance, and the parent Foundation wrapper's
unobserved outer exit, retain their documented limits.
