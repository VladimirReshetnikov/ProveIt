# Source-only review of report 162: induction, marking, and affine rules

Reviewed package: `/tmp/zfc-intake-162/zfc-prefix250-report`.
Reviewer: `opening_encoder`. This review reads source and retained result metadata;
it executes no report checker, suite, proof compiler, dependency build, or version
query. It makes no fresh-PASS claim. The accompanying JSON pins the read inventory.

## Finding

I found no mathematical soundness blocker in the requested three components.
Their universal claims follow from valid ordinary inductions and a sound finite
symbolic execution argument, with the explicit preconditions below. The result
is meaningful new evidence about the existing 250-state table. It is not another
state reduction, a proof-assistant endpoint for that table, or the requested PA
formalization of the ZFC consistency equivalence.

The exact old-label table is SHA-256
`fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43`;
the canonical table is
`0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e`.
The builder checks all rows, the counted states, the unique halting row, and the
canonical relabelling. The supplied source pin is
`80e26b89e905bf3e5dfc322befdc1c6eaf25a109`; the program parser additionally binds
the exact `Prog254.v` bytes to their SHA-256 and Git blob identity. The parent has
separately identified the table with report 161; I did not rerun that comparison.

## Macro induction checker

`check_macro_inductions.py:133-168` has two execution rules. A literal step is
allowed only when the leading run is provably nonempty. A whole-run scan is
allowed only for a table self-loop that moves in the scan direction. All run
lengths have nonnegative affine coefficients and constants. Thus the scan has a
valid zero case and a successor case consisting of one literal transition and
the induction hypothesis, including when a variable is zero. It does not infer
an unbounded run from sampled unary lengths.

The four one-block proofs (`:217-237`) use opaque left and right contexts and
stop before inspecting either exterior. Their endpoints preserve state and
orientation and cross exactly one block. The finite-list lift (`:171-192`) is
therefore a valid structural induction. `width_pre` and `width_suf` denote the
sum of actual block widths, not extra machine inputs. Treating those widths as
formal nonnegative quantities does not weaken the universal argument: every
actual list instantiates them, and B/C encodings have the same width.

The identity `C(A)1 = 1B(A)` is valid by list induction. The code (`:239-251`)
checks its empty and one-block identities, then enables a rewrite using that
ordinary cons argument; the cons proof is explained in code comments and the
manuscript, rather than checked by a general logical kernel. This distinction
belongs in any description of the certificate. It is not a defect in the
mathematical argument. Its reversed form is also correct.

Composition proves positive decrement in `2*w(prefix)+4` transitions, zero
decrement in `2*w(prefix)+7`, and increment in `2*w(file)+7`. The selected positive
value is represented as `x+1`, covering all positive naturals. Positive decrement
returns at the old file origin, writes one there, and moves the new file origin
one cell right. Zero decrement restores the entire file and returns in state
112, not the old interpreter's state 3. Increment appends exactly a value-one
spare block, preserving old spare values. These distinctions are retained in
the affine oracle.

Necessary premises are finite natural-valued blocks; a valid marked selected
block; an arbitrary untouched left exterior; blank tape beyond the finite file
for increment; and a following block for zero decrement. The global nine-primary
plus nonempty-spare invariant supplies the last premise for every primary.
Positive decrement does not itself need the spare premise. None of these is a
finite-capacity or bounded-register assumption.

The nine marking cases (`:274-299`) use separate formal natural lengths for all
primary registers. They use literal steps and unary induction only. They verify
the final complete word and displacement. A minor certificate distinction:
`prove_marks` computes and records its time expression, but does not assert that
expression against a separately constructed `2*w(prefix)+3`. The explicit
marking induction below establishes that formula. The actual symbolic marking
input uses a blank far-right exterior; no rule reaches it, so the stronger
arbitrary-exterior claim follows from locality, also proved separately below.

## Marking transport

`audit_marking_transport.py:29-41,55-61` enumerates exactly 24 transition pairs
and compares their writes, directions, and successors in both tables. The
footprint excludes all changed/new carry and pulse states.

`marking_transport.tex:41-81` proves the required footprint containment. It
crosses each preceding `01^(v+1)` block in `v+2` steps, erases exactly the first
one of the selected block, and traverses preceding blocks in reverse. It stops
at the left exterior before executing a transition there. The exact result is
state 2 for selector 0 and state 6 otherwise, head `h-1`, with duration
`2*w(prefix)+3`. Both exterior contexts are arbitrary and preserved; the suffix
may be empty. Marking itself does not need a spare. The spare requirement belongs
to zero decrement, as the manuscript states.

The row comparison alone would not establish that no other row is used. Here
the ordinary footprint proof supplies that missing implication, and the direct
symbolic marking certificates provide a second check on the specialized cases.
There is no reliance on an old increment/decrement theorem whose output differs.

## Affine execution and source binding

`affine_engine.py:32-89` gives each segment `('r', b, a, c)` the meaning
`a*n+c` cells for arbitrary `n >= 0`. Recentring, splitting off a cell when
`c > 0`, removing an identically empty segment, and adding an implicit left
blank cell preserve the represented configuration. Directional self-loops can
cross a whole run by natural-number induction, including zero-length runs.
The finite nonnegative coefficients prevent an unproved positivity test.
Canonicalization merges equal-bit runs and drops only the far-left zero suffix
into an already infinite blank exterior. It preserves the box and its tag.
Equality of canonical descriptions is sufficient for complete-tape equality.

The oracle (`:19-30`) marks only an unchanged plain box, retains the selected
physical register, and requires a matching decrement guard. Post-increment and
post-positive-decrement tags prevent a second opaque update. Zero decrement
can re-mark because it changes no register. The extra one prepended for positive
decrement is exactly the cell at the old box origin, and `onleft = True` puts the
head there relative to the new origin. The literal box-boundary rule reads the
known first zero, permits only an unchanged-zero write and left move, and makes
no assumption about any opaque interior cell. The nonempty-spare invariant is
preserved by every permitted box effect.

The fresh parser (`review_affine_source.py:30-111`) consumes the entire table
body, checks declared root/count, forward child indices, exactly one incoming
edge per nonroot node, all-node reachability, and register bounds. It independently
enumerates every leaf with the physical permutation. Equality with the cache is
entry-by-entry and order-sensitive, not a length-only test. Thus the finite 6,460
leaf list is a complete case split of the pinned 6,459-node program.

The full-width `full_inc` and `full_strip` definitions (`:114-136`) agree with
the bundled `RegisterPath.lean:58-92`, including overflow zero cells. The target
uses budget `n+40+extra+overflow`, so trimmed trailing zeros in the other checker
are explicitly accounted for as gap cells here. The 8,391 guarded cases cover
each decrement branch and every other instruction. The 342 direct oracle checks
also exercise missing/wrong-register guards and forbidden post-effect marking.

Only literal transitions and literal box-boundary steps count toward positive
progress. A successful result therefore denotes a positive finite concrete run
for every gap and guard instance; scans of zero cells cannot produce fake
progress. Fuel exhaustion raises an error. The reported minimum of 13 literal
steps and maximum of 497 symbolic rules are retained-result data, not new results
from this review.

The global use still needs clean source paths, total decoder coverage, budget
at least 40, the physical permutation, nonempty spares, and blank exterior.
The companion argument explicitly explains these premises and the complete-tape
rebasing `P 0^g = Q 0^(B-d)`. The generic positive-segment halting reflection is
an ordinary theorem applicable to the changed invariant; the old concrete Lean
252-state instance does not automatically become a theorem about this table.
The parent/other reviewer own detailed global and set-theoretic calibration
review. No source-only finding here closes the internal PA endpoint.

## Exact substantive replay recommendation

Use an isolated copy of the package and run the existing nine-check entry point
once, with assertions enabled and an external wall-time bound, for example:

```sh
env -u PYTHONOPTIMIZE PYTHONDONTWRITEBYTECODE=1 timeout 180s python3 -B code/verify.py
```

The working directory must be the isolated package copy. The entry point itself
resolves its children against that package root. Preserve stdout, stderr, exit
code, the freshly written summary, and every per-check result; distinguish them
from the supplied author results. No need to run an additional search or broad
parameter sweep after all nine checks pass. The package's reported 28.53-second
runtime is author evidence, not a promised bound for this environment.

The nine checks are reconstruction; four block/three macro/nine marking
inductions; all guarded instructions; exact marking footprint; independent full
source/full PC audit; dual bootstrap; independent retiming; literal instruction
regressions; and literal macro regressions. The full-source command must use
`sources/prior/instruction-sites-physical.json`, not the logical-operand
`results/instruction-sites.json`, with `--checker code/affine_engine.py`.
All are substantive here: the first seven support separate mathematical
premises; the final two are finite implementation regressions and must remain
labelled as such. No proof compiler, dependency rebuild, checksum-manifest
validation, or simulation-to-nonhalting inference is part of this replay.

Minor nonblocking documentation/robustness points: the source-review script's
header still names `prefix_affine`, while the actual suite supplies
`affine_engine.py`. Also the standalone marking auditor does not reject `-O`
itself. The prescribed suite rejects optimized mode before launching children
and removes `PYTHONOPTIMIZE`; its assertions therefore remain active. These do
not invalidate the specified run or the mathematical proof.
