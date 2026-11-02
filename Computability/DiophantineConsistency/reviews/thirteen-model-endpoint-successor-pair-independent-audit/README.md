# Independent paired source-current endpoint audit

The read-only [audit](audit.py) of evidence commit `2ea5025234` actually
exited 0 in session 89120; its [receipt](CHECK.json) and
[terminal observation](terminal-observation.json) record the result. It
checked all 684 recorded compiler and dependency-query exits, commands,
topological direct imports, source/object/log hashes and every log in the
tracked archive. Both sides have matching source, object and log hashes for
each of 342 modules. It checked 807 historical seed modules per side, their
recorded output companions and the current project-object inventory, the
9,430 recorded direct guard paths, the plan's seed/output and external
guards, and a successful independent plan-audit rerun. The author's actual
outer session 90536 is recorded as exit 0 at launch HEAD `ca3a38b569`.
No Lean compilation was rerun for this review.

Both explicit inventories contain exactly the intended eight declaration
names: `ModelThirteenCarrier.complete`, `sameNoZero69`, `bridge69`, its
native, standard and reference equivalences, and `Model69EndpointBindingDraft`
`eval_equal` and `shifted_zero_equal`. The evaluation equality reports
`propext` and `Quot.sound`; the other seven report `propext`,
`Classical.choice`, and `Quot.sound`. These are Lean metatheory dependencies.
Each side's 128 warning lines in 33 modules classify as 36 unused section
variables, 5 unused variables, 51 unused simp arguments, 3 simp suggestions,
17 deprecations, 6 unused tactics, 3 unreachable tactics, 3 sequencing
suggestions and 4 simp-indexing performance notices. The logs contain no
`sorry`, `sorryAx`, or compiler errors.

The checked native and standard iPRA theorems are stated for
`positiveShift (expressionAt69 CurrentWindowCarry2011.ports)` and conclude
`nativeNoZero` iff the negation of `mappedNativeRefutation embedding`;
the latter is the native translation of the mapped positive Foundation ZFC
refutation predicate. The reference theorem states the corresponding erased
formula. The compiled binding proves ring-evaluation equality with the
69-node literal and equality of shifted **model-zero predicates**. This pair
does not itself contain a syntactic iPRA proof transferring `nativeNoZero`
to `Thirteen69Cuts.currentLiteral`; a separate DAG-specific client is needed.
Nor do these checks alone bind an external JSON equation presentation to
that internal formula.

The retained prefix/window and Foundation outer-wrapper provenance limits,
package-transitive/dynamic ancestry, and mutations between checks remain.
Compilation resource monitoring is sampled; `lean --deps` has a 120-second
leader timeout but no sampled RSS/disk or explicit descendant-group cleanup.
Upstream additions `ModelThirteenCarrierChecks.lean` in `ec42d7f83b` and
`ModelThirteenChecks`, `ModelThirteenForms`, `ModelThirteenSquares`, and
`ModelThirteenStrong` in `6f8dd13085` postdate this frozen replay and are not
covered by it.
