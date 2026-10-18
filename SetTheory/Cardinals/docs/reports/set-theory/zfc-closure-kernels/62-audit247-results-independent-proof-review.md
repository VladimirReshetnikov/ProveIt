# Independent review of the 247-state construction

## Scope and exact object

This review concerns the unchanged-initializer candidate, whose old-label SHA-256 is
`0d37614f3caf37139b0be127837630539224acd1c45d748cf5704abfc3230b42`
and whose canonical SHA-256 is
`58bbbda620daf6d4d62f486db05f54d0dccb8373c080c1b5a0b26533e7a3a669`.
It is obtained from the frozen Prefix250 table (old-label SHA-256
`fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43`)
by changing just `(60,0): (0,R,0)` to `(0,R,20)` and deleting states
`0,1,3`. Start 97 and its initialization row `(97,0)=(1,R,83)` are unchanged.
The separate halt label is 254. There are 247 working states and 494 rows.

The independent standard-library audit reconstructs both files from that recipe,
compares their complete bytes with the supplied candidates, parses the supplied
old-label file independently, and executes its actual transitions on a dense tape.
The source 250 file is pinned by its full digest. It checks graph reachability,
ordinary exact bisimulation, the complete marking support rows, incoming-edge facts,
and every cell of the final bootstrap tape. No search driver or accelerated
register oracle is used by this finite replay.

## Universal marking identity

Let `B(v)=0 1^(v+1)`, for every natural number v. Thus every valid block has a
separator0 followed by at least one1. Put

`S=[60,44,31,56,38,40,28,64,69]`.

For each index j, the read-1 row of S[j] preserves1 and moves right into S[j].
For j>0, its read-0 row preserves0 and moves right into S[j-1].
Originally S[0]=60 had read-0 successor 0; after the patch it has successor 20.
These finite row facts (the read-1 and read-0 selector rows and the marker
continuations) are direct table properties; the audit checks
all required equations, not an inferred numeric state-name convention.

Suppose a marking call begins in S[r] at the first separator of
`B(v0)...B(v(n-1))`, where 0<=r<9 and n>=9. Induction on r, using the preserving
right self-loops, shows that the first transition into state 0 in the old
routine is made from state 60 at the separator of B(vr). In particular its
new head position contains 1. The incoming table fact alone does **not** imply
this read-bit guarantee on arbitrary tapes; the valid-block hypothesis is
necessary and is exactly the inherited register-frame invariant.

At a selected separator x, the only changed local computation is

- Prefix250: `60@x, 01 -> 0@(x+1), 01 -> 2@x, 00`.
- Prefix247: `60@x, 01 -> 20@(x+1), 01 -> 2@x, 00`.

The second step agrees because both old `(0,1)` and retained `(20,1)` equal
`(0,L,2)`. The two trajectories have exactly the same endpoint, elapsed time,
and entire tape, including arbitrary exterior cells. No assumption on vr's
magnitude, the preceding registers, or the spare suffix is used beyond validity.
The inherited rest of the marking return routine is unchanged. Consequently
its complete old contract transfers to the new table.

## Why two more states disappear

The complete incoming-edge lists in Prefix250 are

- into 0: `(60,0)`;
- into 1: `(0,0)`, `(1,1)`, `(3,1)`;
- into 3: `(1,0)`.

After the redirection away from0, states 1 and 3 have no incoming edge from
outside the set {1,3}. Since the initial state 97 is outside that set, an ordinary
induction on time proves them graph-unreachable in the modified machine, on
**every** tape. Deleting them is therefore globally safe and requires no
assumption about the blank startup. The same graph argument applies from any
valid runtime root in state 96.

For the comparison with Prefix250 from a valid runtime root, state 0 is reached
only through a marking call, and that call reads 1 there. Prefix250 therefore
does not take `(0,0)` after a legal root, and cannot enter 1 or 3. This conclusion
uses the complete instruction/carry contract decomposition: register selection
uses the marking contract above, while the shared prefix carry circuits do not
contain state 0. The full symbolic instruction replay must retain all 8,391
original guards. A finite literal sample is not a replacement for that
decomposition or for the unbounded block identities.

At corresponding runtime configurations, map old state 0 to 20 and all other
visited states identically. The map preserves every actual transition on a
legal computation. Equivalently, replace each displayed two-step marker block
by the equal two-step block and leave all other literal steps unchanged.
In either presentation, the tape and head remain identical, no halting state
is hidden in a comparison block, and halting is preserved in both directions.
No clock rescaling is required from a common legal root.

## Bootstrap is a separate finite certificate

The patch changes the behavior of dirty startup tapes. One must therefore replay
the new blank machine; the older 585,431-step Prefix250 bootstrap is not a
certificate for this table. The independent dense replay performs 741,241 literal
transitions, sees no earlier halt, and reaches old state 96 (canonical 89), head -5,
with marker -6 and header 245. Every PC cell from -5 through 244 is 0, giving gap 250.
The complete set of1 positions is

`{-6,245,247,249,251,253,254,255,256,258,260,262,263,264,265,267,269}`

union

`{271+3j,272+3j : 0<=j<235}`.

All other cells are zero. This has 487 ones and rightmost one 974. Decoding it
produces physical primary registers `[0,0,0,3,0,0,3,0,0]` followed by 235 spare
blocks, each of value 1. The complete dense tape is repainted from this description
and compared byte-for-byte, so the assertion includes all unused exterior cells.

The logical-to-physical map `[6,2,0,4,3,7,8,5,1]` gives logical registers
`(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`. The formula fields T,H and stack W are
all zero. The spare invariant is satisfied with 235 nonempty valid spare blocks.
Gap 250 exceeds the runtime minimum 40. There is no prepared input, additional
startup state, or added symbol.

The global initializer reuse argument remains intact: the only incoming edge
to 97 is `(255,0)`, and the only incoming edge to 255 is `(75,0)`. The latter writes 1
before moving right, and the former returns left to that same cell. Thus every
recurrent entry to 97 reads 1. The independent finite run also observes `(97,0)`
exactly once, but the incoming-edge argument is what proves this for the entire
future run.

## Exact logical specialization and proof boundary

The existing theorem `DirtyProgram254.six_nonformula_path_iff` quantifies
`N A D X Y L` and initializes the logical state
`(N,0,0,A,D,0,X,Y,L)`. The exact instantiation for this candidate is

`DirtyProgram254.six_nonformula_path_iff 3 0 3 0 0 0`.

It admits the nonzero numerical parameter D=3; this field is not a formula or
stack. The universal literal-program/path-DAG comparison is also required
before applying that theorem. The source semantic/calibration arguments then
identify halting with a finite ZFC refutation.

The new marking identity, dead-component deletion, finite bootstrap certificate,
and induction composing the runtime are ordinary mathematical arguments
formalizable in ZFC. The finite audit does not itself prove the unbounded
runtime theorem or implement ZFC proof-code translation. The construction must
not be described as a new kernel-checked Lean endpoint, a serialized internal
ZFC derivation, or a PA-internal equivalence. It inherits the prior runtime and
logical calibration mathematics and supplies a conventional proof for the new
table modification. Full exact state reachability and 247 exact bisimulation
classes provide no lower bound against other semantic reductions.

## Review result

The three-state saving is sound once the original Prefix250 unbounded runtime
contracts and complete guard decomposition are retained. The new mathematical
obligation is only the two-step marking identity above; its hypothesis is an
existing valid-file invariant. The independent finite audit passes the chosen
candidate hashes, exact state count, unchanged final halting action, complete
bootstrap frame, correct logical root, and incoming-edge support. No additional
logical or representation premise was discovered.
