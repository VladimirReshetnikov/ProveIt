# A finite search around the verified 253-state machine

## Outcome and status

**No new blank-tape Turing machine with fewer than 253 working states was established.**
This bundle contains a reproducible engineering search, a finite invariant for
the published register program, and three new guarded detours of the known
252-state prepared-tape runtime body. These are runtime variants, **not**
252-state machines proved equivalent to consistency of ZFC.

The public 253-state reference is mira-emmy's reduction at commit
`0d544f2a2e3c18f12278441a74b7879f31cbe856`, described in public PR 20:
<https://github.com/jeff87654/busy-beaver/pull/20>.
The 254-state machine was designed by Mira-Cult; Jeff supplied the formal
verification. The frozen input URLs, byte lengths and SHA256 hashes are in
`PROVENANCE.json`; upstream attribution notices are retained in `sources/`.
The ProveIt snapshot inspected was
`4747142d5d15213eb711bdadfa3cc7e769fcb7a7`.

All Python checks here are executable mathematical audits. They are not a new
Coq or Lean kernel verification. The public machine's separate formal proof
is not rebuilt by this bundle. A checker rejection is not a proof that the
candidate is semantically wrong: some failures are the symbolic executor's
500-step fuel limit or its inability to establish a symbolic operation.

## Precise machine convention and the prepared body

The tape is two-way infinite, binary, and blank outside the specified finite
set of one-cells. A transition is `(state, read) -> (write, L/R, target)`;
there are no stationary moves. A terminal target is not a working state.

We use the original 254-state labels throughout. The working labels are
`{0,...,253} - {5,8}`, giving **252**, despite the larger maximum label.
The sole terminal is old label 254. Starting from the original table, change
`3/0` to `0 L 48`, and delete states 5 and 8. The old `49/1` row is already
`0 R 64`. This is the known prepared runtime reduction of the public 253:
in the latter, old `49/1` goes to the shared startup state 5, whose read-1
behavior is the same as old 64. Its indispensable *initial* read-0 behavior
has not been supplied by the prepared body.

`machines/runtime252.tm` is this literal complete table. Three further tables
replace only `49/1` by `1 L 54`, `1 L 66`, or `1 L 114`. All four files declare
start state **96 for the externally supplied prepared seed**. Their headers
explicitly disclaim a blank-tape consistency claim. `machines/prepared_seed.json`
has head 0, marker at -1, header at 40, initial PC empty, and physical registers
`[0,0,0,0,0,0,2,0,0]`; it is a finite nonblank input. Table hashes are in
`runtime_variant_manifest.json`. Running one of these files from a blank tape
in its declared state 96 is not the verified prepared computation.

## What “affine-valid” means in these experiments

There are 6,460 leaves in the exact published register-program tree. The audit
checks both outcomes of every decrement, giving **8,391 instruction cases**.
For each leaf path `Q`, it starts the literal candidate table at old dispatch
state 96 with head on the first PC cell and frame

`0^infinity  1  Q  0^(n + 40 - |Q|)  1  sepsR(vs)  0^infinity`,

for a free integer `n >= 0` and **every** list `vs` of at least nine natural
register values. The maximum leaf depth is 34. Here
`sepsR(vs) = concatenation of 0 1^(v+1) over v in vs`.
The first nine blocks are physical registers; the remaining blocks are an
arbitrary finite tail, not assumed all zero. The source-register indices in
physical order are `[2,4,3,7,6,8,0,1,5]` (wffstack, param1, axiomcode,
scratch2, scratch1, prooflist, nextproof, topwff, param2).

The pinned symbolic executor represents a run as `a*n+c` identical bits,
uses exact integer arithmetic, and scans a whole self-loop run at once.
Peeling a symbolic run requires a strictly positive constant lower bound.
The target is exact: return to state 96 with the prescribed next PC, marker,
header distance, and register effect. An overflow moves the marker one cell
left and increases the available header distance by one. It does not merely
check the first visit to dispatch. The halt leaf must reach old terminal 254.
Each decrement branch carries its declared zero/positive hypothesis.

The four inherited register-box contracts are:

| Entry | Required file | Exit one cell left of the file | Resulting file |
|---|---|---|---|
| Skip state `S_r`, `r < 9` | Plain `sepsR(vs)`, length >= 9 | State 2 if r=0, else 6 | `sepsM(r,vs)`, first 1 of block r erased |
| 73 | `sepsM(r,vs)`, r<9 | State 48 | `sepsR(incr(r,vs))` |
| 43, zero branch | `sepsM(r,vs)`, vs[r]=0 | State 3 | `sepsR(vs)` |
| 43, positive branch | `sepsM(r,vs)`, vs[r]>0 | State 63 if r=0, else 48 | `sepsR(decr(r,vs) ++ [0])` |

The skip states `S_0,...,S_8` are `[60,44,31,56,38,40,28,64,69]`.
Left context is unchanged. Increment preserves file length; positive decrement
appends one zero-valued spare block. The executor may also read the file's
known first zero while moving left, using the actual transition.

For the principal single-row search, **55 transition rows are kept literally
unchanged**, sufficient to preserve the published box contracts: both rows of
states `{0,1,2,3,4,6,28,31,38,40,43,44,48,56,59,60,63,64,69,73,75,83,85,95,97,109,112,131}`,
except `3/0`. That exception is an exterior return action; the zero-decrement
box stops before it executes. Changing an unexamined internal box row and
continuing to trust the old oracle would be invalid; the main search does not
do that. The earlier exploratory *core-fold* search explicitly uses relabelled
box interfaces plus finite concrete probes, and has a weaker rejection scope.
Its sole survivor is the already known 5 -> 64 runtime fold.

An accepted mutation passes every baseline instruction case that reads its
changed entry. All other baseline cases have an identical deterministic
execution: a first changed transition could not occur without that same
entry appearing in the baseline trace. This justifies the affected-case
optimization. Every case uses at most **500 abstract executor fuel units**.
The pinned Python executor is evidence under the published box contracts,
not itself a newly kernel-checked equivalence theorem.

## Search domains and exact results

| Experiment | Actual checks | Outcome |
|---|---:|---|
| Core-state redirects, relabelled box interface | 7,169 candidates; 81 finite box probes each when reached, then affine sites | Only old 5 -> 64, the known prepared252 body |
| Mixed read-0/read-1 row merges among 223 unprotected states | 48,982 mutations; 524 equal-row duplicates skipped | No survivor |
| Distinct target per predecessor, 90 eligible states | 26,460 independent-edge trials; 30 combined elimination candidates | No survivor |
| Direct folds after abstract reachability removed 6 cases | 56,196 mutations against 8,385 cases | No survivor |
| Full action replacement of old `49/1` after deleting old 5 | 1,008 actions including the existing action | Four accepted: original plus the three detours |
| All one-row extensions of the prepared252 body | **453,939 mutations** | **707 accepted runtime variants** |

The last domain is exact: 449 nonprotected transition entries, each with
4 write/move choices times 253 destinations (252 working states plus terminal),
minus its original action: `449 * (4*253 - 1) = 453939`.

The predecessor experiment is a staged search: each incoming edge first has
to work with the other incoming edges unchanged; combinations are tried only
after that filter. It is not exhaustive simultaneous transition synthesis.
The core probe family consists of 3 fixed register vectors, 9 indices and 3
operations, with a 2,000-move cap per concrete box test. It is a rejection
filter, not a universal proof for altered box internals.

### Blank-tape phase of the 707-variant search

For each accepted variant, all **252** possible blank initial states were
classified before the first write of 1. A prefix writing only zeros on the
blank tape changes neither the tape nor any relative geometry. It therefore
ends either at a first-write state (unique up to translation) or in a cycle of
zero-writing state transitions. The latter is an exact infinite run on the
blank tape, including cycles with nonzero net head displacement. There were
no halts before the first write. The quick verifier recomputes this entire
classification directly from all 707 tables.

Across **178,164** initial-state choices, **8,487** are zero-only cycles;
**169,677** reduce to **4,951** first-write representatives. Each representative
was simulated for up to **3,000,000 literal TM moves**:

| Representative outcome | Count |
|---|---:|
| Certified entry into a self-loop toward a blank ray | 2,845 |
| Fuel cap reached | 2,106 |
| Halt, finite-array bound, or other termination | 0 |
| Candidate dispatch frame with gap >= 40 | 0 |

The ray certificates have prefixes of at most **1,045** moves. If the head is
on a zero, the next state equals the current state, and the ray in the movement
direction contains only zeros, the machine runs forever regardless of the
symbol written behind it. `quick_verify.py` replays every short prefix and
checks the exact ray condition. The total recorded literal moves over all
representatives is **6,318,032,976**.

The **2,106 capped runs remain unresolved** beyond their finite observations.
They have not been proved infinite, incorrect, or equivalent to one another.
No inference of minimality, or of a universal obstruction to 252 states,
follows from the finite cap.

The C++ simulator stores a 2,000,000-cell array with origin at index 1,000,000.
It stops if the head moves to index <10 or to index >=1,999,500, retaining a
margin for frame reads. No tested run reached this bound. All writes and all
nonzero cells are tracked exactly inside this region; the tested finite
prefixes therefore coincide with the infinite-tape semantics. Small exact
translation-cycle detection was also available (fewer than 30 ones, at most
2,000 stored configurations); it found no additional representative outcome.

### Exactly what startup acceptance would recognize

At state 96, with arbitrary absolute head position `h`, require the leftmost
one-cell to be `h-1`. Treat the 34 cells starting at `h` as an arbitrary PC
word. The first one at or after offset 34 must occur at a header offset
`D >= 40`. After that header, parse a complete file of `0 1^(v+1)` blocks,
at least nine, and require no further ones beyond the parsed file.

This deliberately **overapproximates** the desired legal register-program
frame: the first 34 PC bits and all nine primary values may be arbitrary;
spare values may be nonzero. It does not require the canonical initial vector
or that the PC is reachable in the program. Consequently a hit would still
need a finite prefix or a valid cofinal-search argument; it would not itself
establish consistency equivalence. No hit occurred even in this larger class.

Spatial translations are fully allowed, and all header gaps >=40 are tested.
A valid computation using only a smaller gap (such as 37, 38 or 39), a different
encoding, another dispatch convention, or a later startup beyond the fuel cap
could be missed. The chosen interface is the published gap-40 arbitrary-runtime
invariant. The public253 bootstrap itself first has gap37 and subsequently
reaches gap40; our detector would recognize the later frame if reached in
fuel. These results do not rule out a redesigned encoding or a proof using a
different invariant.

## Exact guarded-detour lemma

The only incoming edges of old state 49 are
`34/0 -> 0 R 49` and `79/0 -> 0 R 49`. Hence on every reachable read-1 visit to
49 from any blank initial state, the cell immediately to the left is zero.
If the initial state itself is 49, its initial read is zero, so this exception
does not trigger the changed row.

The original runtime row `49/1 -> 0 R 64` takes one step. For each
`r in {54,66,114}`, replace it with `1 L r`. The exact rows
`r/0 -> 0 R 70` and `70/1 -> 0 R 64` then complete two further steps. The final
state, head and entire tape are exactly the same as after the original one
step. No intermediate state is terminal. Thus the three variants and the
original prepared252 table have the **same blank-start halting behavior for
every choice of initial working state**. This does not identify that behavior
with consistency of ZFC. It explains exactly why these accepted detours cannot
supply the missing initializer by themselves.

## A checked finite invariant of the register program

`abstract_reachability.py` uses the four abstract atoms `{0}`, `{1}`, `{2}` and
`{3,4,...}`. Each register stores a nonempty union of these atoms; program
locations store a product of nine such unions, or an unreachable marker.
Join is componentwise union. It starts from the exact published `R0`:
nextproof 2, every other register 0, at the root PC.

Increment maps the atoms in order to `{1}`, `{2}`, `>=3`, `>=3`.
Positive decrement maps `{1}` to `{0}`, `{2}` to `{1}`, and `>=3` to
`{2} union >=3`; the zero alternative stays exactly `{0}`. Branch infeasibility
is checked by intersection with zero or positive atoms. PC successors are
computed from the literal Coq tree and the published break/continue arithmetic.

The independent verifier does not rerun fixed-point iteration. It checks the
initial vector belongs to its claimed input mask, and verifies closure under
all **8,384 feasible nonterminal transitions**. This proves invariant soundness
by induction on the number of register instructions: each primitive's abstract
transfer contains every concrete successor, and each computed successor is
included in the target mask. The terminal case needs no closure obligation.

It certifies two impossible positive decrement outcomes and four unreachable
leaves (site indices are zero-based in the literal DFS leaf ordering):

| Site | PC | Instruction/branch |
|---|---|---|
| 6316 | `111010010110001100` | physical register 4 (scratch1) positive decrement impossible |
| 6317 | `1110100101100011010` | increment physical register 8 unreachable |
| 6318 | `1110100101100011011` | continue 2 unreachable |
| 6434 | `111111000` | physical register 7 (topwff) positive decrement impossible |
| 6435 | `1111110010` | increment physical register 4 unreachable |
| 6436 | `1111110011` | continue 2 unreachable |

All 474 transition entries exposed by the unrestricted affine runtime audit
remain exposed after these six cases are removed; the invariant does not make
a new runtime table row unused. A repeat of the 56,196 direct folds with these
cases removed also found no accepted fold. The invariant is a small positive
artifact and potential starting point for a stronger relational analysis.

## Reproduction and quick gate

No network access or third-party Python packages are required. Use Python 3.10+
with assertions enabled (do not use `-O`). Run commands in this directory.
The C++ searches require a C++17 compiler.

```sh
python quick_verify.py
```

This gate verifies all manifested bytes, frozen upstream inputs, all 8,391
prepared-runtime cases, the exact four tables and guarded-detour identities,
the independent abstract certificate, all first-write classifications and all
2,845 short ray certificates. It summarizes the archived capped runs rather
than repeating their 6.3 billion moves. The checked output is
`quick_verification.json`.

To reproduce the main search, use a fresh copy of this directory (the scripts
write new result files):

```sh
python single_row_search.py
c++ -O3 -std=c++17 boot_mutations.cpp -o /tmp/zfc_boot_mutations
/tmp/zfc_boot_mutations sources/zfc_254.tm single_row_survivors.tsv 3000000 > single_row_boot_results.jsonl
```

To reproduce the smaller searches or the invariant:

```sh
python core_fold_search.py
python mixed_fold_search.py
python incoming_fold_search.py
python abstract_reachability.py --k 2
python verify_abstract_certificate.py
python reachable_coverage.py
python reachable_fold_search.py
python startup_extension_search.py
python emit_runtime_variants.py
```

Elapsed-time fields are development measurements and will differ. Regenerating
an abstract certificate changes its elapsed-time field and hence its byte hash;
the invariant verifier still checks its mathematical contents. The immutable
manifest is an audit of the delivered snapshot, not an expectation that newly
regenerated timing metadata have identical bytes. `long_common_orbit.cpp` is
an optional exploratory longer-run diagnostic; its finite observations are
not used by the main conclusions or the quick gate.
