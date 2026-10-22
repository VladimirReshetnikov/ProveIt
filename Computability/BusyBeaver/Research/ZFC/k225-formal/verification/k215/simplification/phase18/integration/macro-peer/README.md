# Independent review of shared macro proofs

The four-file prototype is mathematically coherent. Its one-way transfer resource
moves arbitrary-register runs from `dag254` to `dag222` on the shared closed set.
It keeps the changed rotated136/fetch behavior local. No compiler, generator or
supplied script was run by this peer, and no canonical files were edited.

The [review](review.json) binds the exact four candidates to published parent
`7a1273555ba3c2d4f6db087567309f692660ec72`. The [complete diff](candidate.diff)
and [source map](source-map.json) preserve both selections.

The independent [node-table census](finite-graph.json) finds exactly two changed
old-range nodes, 136 and 149. Their fifteen ancestors, including themselves,
leave 204 shared nodes. Every shared node agrees in both programs and has only
leaf children or children in the same set. All 53 transported contract
occurrences begin in that set. `closed_of_bounded` therefore supplies the right
finite kernel obligation; `node_transfer` has the required 254-to222 direction.

The [API map](api-map.json) and [complete declaration checks](complete-declaration-checks.json)
account for every one of the prototype's 89 old222 declared names: 28 exports,
53 transferred contracts and eight local declarations. Complete pure declarations
match the reference, transferred old proof declarations match modulo the program
name, and local declarations are unchanged. This verifies source contracts, not
Lean's inferred types. The shared `AS` intentionally has the identity of `L2.AS`;
old constructor/projection/recursor constants for the separate structure are not
preserved merely by exporting the type. No maintained qualified caller was found.
Fresh tuple construction, record updates, projections, cases and simp clients
remain necessary.

One maintained dependency was missed by the prototype's local import cut:
`L2Root254` uses `Enum254.gate`, `axStack`, `St`, and its enumerator theorems, but
imports only `L2AxiomsEval254`. After the cut its entire macro import chain lacks
`Enum254`. The [consumer/import census](caller-and-imports.json) identifies this
gap. Add `import BusyBeaver.ZFC.Enum254` directly to `L2Root254`; the exact
[one-line repair](necessary-import.diff) is prepared under `necessary-candidate/`
with a [before/after map](necessary-import-map.json). The215 endpoint imports only
the reference macro libraries, so this consumer import does not defeat that cut.

The root then requested retirement of the now-unused local `while_AS` and
`inc_AS`. Their [caller census](unused-helper-census.json) examines all short and
qualified occurrences across four Lean roots after replacing the old222 bodies.
It finds no outside L2K caller. Remaining occurrences belong to the retained
reference L2 helpers, L2Q219, ArithmeticL2, or DirtyRoot254 opening L2. The
[cleanup](unused-helper-cleanup.diff) removes 21 lines/970 bytes, including obsolete
retention prose, and intentionally retains 87 old declared names. Exact copies
are under `cleanup-candidate/`, bound by the [cleanup map](unused-helper-cleanup-map.json).
The separate program reviewer was told to drop the obsolete while compatibility test.

Keep `loop136`: its one caller expresses the actual next-candidate step. Keep
`trCore`: it replaces 53 repeated transfer applications. The finite exclusion
predicate and explicit root proofs remain short and explain their resource;
further proof golf offers little benefit here.

The prototype saves 509 Lean lines/24,370 bytes across its four files. The final
selection must account separately for the two helper retirements and required
consumer import. Its215 endpoint closure grows from174 to178 modules because it
imports reference254 proofs; this is a maintenance saving across the selected
proof library, not an endpoint-closure saving. Fresh acceptance must rebuild all
changed-source descendants and exact endpoint/API profiles. The root reports a
six-library smoke pass; this source review does not independently audit that run.

An owned metadata traversal initially met an unrelated external Foundation import.
The predecessor and error are retained in `history/metadata-v1`; the corrected
reader treats imports outside the four roots as explicit external leaves. The
specific affected254 closure is entirely present. No Lean source failed here.
