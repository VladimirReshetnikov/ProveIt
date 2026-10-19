# Source review of W2/W3 groundwork, c0b55cdc4a

Commit `c0b55cdc4a3e77c9d21cdec2c542ac4693dfbe9a`, included in fetched/merged
`f70dc9b164b018a97578d49e3fcaf1acb77b46e1`, provides useful represented-interpreter
groundwork and resolves the earlier register-coordinate mismatch in its new
data path. It does **not** yet establish the concrete internal halting
equivalence or the binary240 PA endpoint. No mathematical blocker was found in
the new generic constructions or the changed W1 argument on this source read.
Compilation, performance and axiom auditing were not performed or inferred.

The nine exact commit files, Git blob identities and SHA256 values are retained
in `inputs.json` and `source/`; `commit.diff` preserves the complete change.
`static-census-v2.json` records 19,031 reviewer-owned literal/source checks.
No supplied program, generator, checker or proof compiler was invoked.

## Exact scope and register coordinates

`ArithmeticControlFile.lean` separates the nine-field Cantor tuple, selection,
one-field updates, opcode effects and nonzero live-state encoding from the
Prog254 catalogue. The entire Tuple section and the live definitions match
`ArithmeticControlStep254` exactly. The final `live_decode` proof has the same
statement but is locally reconstructed from IOpen arithmetic, rather than
calling `ArithmeticRow254.pred_add_one`; “proofs copied verbatim” would therefore
be too strong. These definitions do not by themselves identify logical source
registers with physical fields.

That identification is explicit in `ArithmeticControlTree.lean:196–217`:
`registerOf` applies `Permutation252Frame.physOf`. In
`emit_bisim_cert.py:17–38`, **both** logical catalogues are converted with the
identical permutation before exploration computes offsets. The map is
`0→6, 1→2, 2→0, 3→4, 4→3, 5→7, 6→8, 7→5, 8→1`.
The literal certificate has 3,862 entries, ten with a unit offset, all on its
B side at physical positions 6 or 7 (logical registers 0 or 5). Its initial
entry is controls 1/1 with zero offsets, and every successor index is in range.
These are static data checks, **not** checks of the 3,862 semantic obligations.
The earlier W1 physical/logical mismatch is addressed for this new certificate;
later logical scheduler and binary-frame interfaces still need explicit
encoding equalities and initial-state linkage.

`ControlCatalogue.entry_at_crank` relates count-guided tree descent to the
false-first leaf list, conditional on a successful `twalk`. `BT.get_ofList`
proves balanced lookup matches list lookup. `ArithmeticControlTree` represents
fixed tables by Σ0 formulas, one step by a Σ1 formula (IOpen), and runs at all
internal times by Σ1 primitive recursion (IΣ1). Its `spec` theorem at lines
508–515 requires the catalogue length and a known row; it proves agreement
between this represented step and the generic row semantics. It is not yet an
internal theorem relating structured `RMDag.Run`, scheduler semantics, or the
binary machine to that interpreter. In particular, `spec` is self-contained
row semantics even for partial trees; a source-path bridge must separately
discharge successful decoding, tree completeness and register-range facts.
The concrete DAG has only registers 0–8.

The revised `ArithmeticControlBisim.halts_iff_of_check` still applies in every
IΣ1 model with arbitrary internal files and times. It requires represented run
laws, matching row-step specifications, a common definable file algebra,
nonzero live states, and `entryOK` for **every** index below N. `entryOK` now
includes positive A-control and bounded successors; `checkFrom_entry` is the
bridge from separately checked ranges to that universal premise. The positive
segment-clock argument remains unchanged.

## Concrete status, counts and findings

`ControlBisimRotation240.lean:18–28` currently claims a concrete `halts_iff`
and a complete chunk check. Its declarations end at `check_probe : chunk 0 10
= true` (line 69); there is no concrete `halts_iff`, no all-entry check, and no
application of `halts_iff_of_check`. `rows_probe` only checks the final row of
each table exists. The generated certificate header at line 10 and the emitter
header text also describe all-entry kernel checking as already occurring.
The commit message correctly describes the full check/equivalence as pending.

Suggested narrow documentation replacement:

> Defines the dag254 and Rotation240 catalogue instances and a generated
> 3,862-entry certificate. The current source contains length/row probes and a
> kernel proof for entries 0–9. Complete chunk checking and instantiation of
> the internal halting-equivalence theorem remain pending.

For the generated header, use “The complete certificate is intended to be
kernel-checked in ControlBisimRotation240; the present wrapper checks its first
ten entries.” No proof edits are needed to correct these descriptions.

The apparent 6,459/6,460 discrepancy is not a contradiction: independently
unfolding the **literal DAG data**, without running the machine, gives 6,459
binary-node occurrences and 6,460 instruction leaves, including one halt.
All 219 DAG nodes are reachable; maximum unfolding depth is 96, below fuel
220. The full binary-tree identity explains the one-element difference.
`check_templates.py` visits node occurrences, not leaves. Its intended
context-independent-block analysis is useful evidence for a future internal
structured-semantics port, but remains external: it merely prints its `bad`
counter (lines 96–116), without failing the process when it is nonzero. A
future runner must inspect that counter or use a preserved strict successor;
exit zero alone is not verification of that claim.

Nondefault settings must remain explicit: ArithmeticControlFile/Tree/Bisim
set depth 8,192 and heartbeats 4,000,000; ControlBisimRotation240 sets depth
100,000 and unlimited heartbeats; all ten certificate parts locally set depth
200,000 and unlimited heartbeats. `decide +kernel` is used, not `native_decide`.
No new proof holes/axioms were found outside comments in the six changed Lean
files. The commit adds no fresh command log, verification record or typed
audit. Source presence is not a new bounded/default-limit PASS claim.

## Remaining work and live-coverage separation

The new left side is the unfolding of `ofDag dag254 219`, **not** the previous
Prog254 numbered interpreter. This makes the existing L2 DAG contracts a
natural source for a future internal port, but the ordinary Nat-valued
`RMEquiv.halts_iff_iterHalts` (`RMEquiv.lean:640`) and external template checks
cannot establish its arbitrary-model version. The old Prog254 contracts also
cannot be reused against the new control numbers without an explicit bridge.

The immediate next proof work is complete, bounded chunk verification of all
3,862 entries, range assembly and the concrete generic-theorem instantiation.
Then the DAG structured/scheduler connection and its model-internal contracts,
the Rotation240 interpreter-to-binary simulation, the exact startup encoding,
and final PA composition/audit remain. Existing validator consistency results
close a different component; they do not supply these operational bridges.
W2 is therefore substantial groundwork, W3 remains partial, and W4–W7 require
the revised DAG route rather than silently retaining the old Prog254 diagram.

Own import inspection finds 44 BusyBeaver modules in the wrapper closure,
with no `Sites*` module and no `ArithmeticControlData254`. Imports outside that
project root were recorded but not traversed; this is not a provider-object
inventory. Root separately reported zero intersections between the nine
changed paths and its 1,963 frozen live/prospective/protected coverage paths.
The external decoder-coverage proof remains useful and logically separate.
No repository file was edited by this review, and no PA-lane implementation
was undertaken.

Reviewer role: drop_contract, author/reviewer of earlier external bootstrap,
frame, endpoint and W1 integration material; not author of this upstream
commit. The initial inline import census mistook a comment beginning “import
closures)” for an import. That preliminary `static-census.json` is retained;
the selected reviewer strips nested Lean comments and records the corrected
result in `static-census-v2.json`. No supplied source or result was changed.

## Publication

The [exact review receipt](review.json) and [lossless source/review history](history.json.gz) retain the original upstream bytes, including the preliminary census and corrected reader. This publication also corrects the concrete wrapper and generated certificate headers (and the emitter text) to describe the first-ten-entry probe accurately. No theorem, certificate entry, or checking algorithm changes; the all-entry proof remains pending.
