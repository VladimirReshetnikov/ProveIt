# Author-only standard iPRA endpoint for the 40-variable quartic

The second guarded build, tool session `86717`, actually exited 0 with
`PASS_AUTHOR_STANDARD_QM40`. It rebuilt `IPRASuccessorInduction`,
`IPRAAddOneGeneral`, `IPRASuccessorInductionConverse` and
`IPRAStandardTheory` on the completed quartic-native author provider, then
compiled `IPRAStandardQM40`. The last module proves in Lean the existence of
standard-iPRA derivations in both directions between its positive-shifted
40-variable quartic no-zero sentence and the negated mapped native ZFC
refutation predicate; it also connects that predicate with the
Gödel–Gentzen translation of the selected Foundation ZFC consistency sentence.
The source's initial “uncompiled” comment is stale; the source bytes were
retained unchanged for this build.

This is a **single-author incremental build**, not a paired replay or a
fully authenticated current-source closure. Its native and model providers,
package/transitive/dynamic ancestry and point-in-time guard limitations are
inherited. The result is about the formal arithmetic expression in Lean; it
does not establish a semantics of PDF bytes or a new claim about the separate
12-variable compact44 endpoint.

The source-pinned standard theory emitted exactly three historical unused-simp
warnings. The driver accepts them only when the **complete** log, after
normalizing the source path, equals the SHA-pinned historical log. A no-Lean
comparison passed and a log with an appended warning did not match. All other
warnings and all errors or `sorryAx` are rejected. The final client log has
no warnings and prints precisely the three named theorems with Lean
metatheory axioms `propext`, `Classical.choice` and `Quot.sound`; these are
not added object-theory axioms.

The first run, tool session `80964`, exited 1 after three successful modules:
`IPRAStandardTheory` itself produced its historical warnings and was rejected
by the original warning-free policy. The exact failed driver, preflight,
failure record and all four logs are retained in `observations/attempt01/`;
the fourth compiled object was not accepted as a completed step. The second
run's frozen sources, logs, per-module records, direct guards, preflight and
result are retained in `observations/attempt02/`. The full successful result
SHA-256 is `0d77e6da49ebad57c6808fa1f38aefedef7d790ae620f6cc6c61749be705339a`;
the resulting `IPRAStandardQM40.olean` SHA-256 is
`91fb38eb57f4a3e769690db4999502fd1f65defdedff266208a5649efa9d3679`.

The author-side no-Lean `audit.py` checks the retained and live result,
source/log snapshots, recorded direct guards, exact warning baseline, and
three named final axiom reports. It exited 0. This is a post-run author
artifact check, not an independent Lean run or verification of the full
transitive dependency closure. The runner uses a separate fresh symlink
overlay, direct-input and companion guards, `-M3000 -j1`, a 600-second
timeout per compiler child, and never mutates the native provider.
