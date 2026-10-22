# Fourteenth K215 proof-simplification checkpoint

The [phase-fifteen successor](../phase15/README.md) now provides the current
recursion, quotient-syntax and small-interface proofs. This page and its packet
remain the exact phase14 record. Its optional current-repository check requires
the frozen phase14 sources; use historical mode after later adoptions.

The named calculi now share their derived-rule proofs, and the profile contracts
are proved once under transitive containers. This removes repeated mathematical
arguments and the generated `KProfileTC` duplicate. The exact 215-state machine,
both endpoint statements and their axiom profiles are unchanged.

The seven selected Lean sources and retirement of `KProfileTC.lean` remove
**12,116 bytes and 243 lines**. Retiring its generator removes another
**3,067 bytes and 71 lines**. The endpoint shrinks from **179 to 178 project
modules**, selecting **2,093,112 bytes** of source rather than 2,105,228. Five
additional decoder-prefix modules remain separately checked.

The derived-rule sources follow the [attributed `ac61181` proposal](../phase13/upstream-merge/README.md),
with one sole-use wrapper inlined. The shared proofs take their propositional
support explicitly as `hC`; `Rows` supplies quantifier and atomic-rewriting rules
for both `Thm` and `ThmK`. Equality-free, quantifier-free, helper-binder and freshness
premises remain explicit. The profile sources follow
[`5423911775`](../phase13/upstream-merge/later-542391/merge.json): the six contracts
use `TransContainers` directly, with the stronger `Containers` specialization
preserved. The guarded tagged-domain interfaces retain their hypotheses. Shared
helper APIs change, while maintained endpoint and compatibility interfaces pass
explicit typed clients. The phase-thirteen implication core, numerical adapter,
Lukasiewicz module and their producer/input boundary remain unchanged.

Both serialized incremental checks pass with observed outer exit zero:

| Scope | New or retained compilation evidence | Typed checks |
| --- | --- | --- |
| Primary: 183 project modules plus seven API clients (190 providers) | 65 successful fresh invocations from the first attempt, one corrected client in the retry, and 124 exact phase-thirteen providers | 20 existing API reports and 14 new reports; two freshly compiled endpoint clients with ten exact reports |
| Compatibility: 68 project modules plus two clients (70 providers) | 16 fresh, 53 current-primary providers and one phase-thirteen `Dag254` | Ten old-client reports and five existing `WFTheory` reports |

Together these scopes bind **198 distinct project modules**. Source changes force
all affected descendants to recompile, even through byte-identical intermediate
objects. All nine physical-site batches retain their exact unchanged source/import
bindings and **6,176 outcomes**; they were not rerun in this checkpoint.

The 14 new API reports comprise one axiom-free report, five using only `propext`,
and eight using exactly `propext`, `Classical.choice` and `Quot.sound`. The 20 older
API reports, ten endpoint reports and ten compatibility-client profiles retain
their exact previous assumptions. Every API and endpoint client has zero warnings.
Primary project logs contain 20 preexisting warning occurrences: 19 in the selected
fresh records and one inherited. Compatibility logs contain seven: one fresh and
six inherited. The [warning comparison](integration/warning-comparison.json)
binds each occurrence to identical phase-thirteen source.

The first primary attempt failed only in the new profile audit client: its
structure-field equation omitted three implicit binders. The 189 providers,
including all seven production candidates, had passed. The failed client's
elaboration output, including `sorryAx`, is retained as failure evidence and is
excluded from every accepted provider. Adding the three binders changed no theorem
statement or production source. A reviewed initializer revalidated the 189 successful
records without turning the failed run into a pass. The retry compiled only the
corrected client and the two endpoint audits. Both attempts and the exact resume
provenance are retained.

[Root's actual review](integration/root-actual-review.json),
[adoption](integration/adoption.json) and [current-source binding](integration/current-review.json)
record the seven exact checked source replacements and two retirements, including
their before-bytes. The compact [Lean execution packet](lean/README.md) preserves
the raw checks and failure history. Its owner and independent saved-reader checks
both pass against the current repository sources. No supplied generator or renderer
was executed for this adoption.

The [previous checkpoint](../phase13/README.md) remains an immutable historical
record. This checkpoint makes no Rocq production change, internal PA endpoint,
new machine or minimality claim. Primitive/return factoring and later intake
proposals keep their separate proof obligations.
