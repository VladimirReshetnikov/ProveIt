# Runtime and source redesign experiments

**No machine with fewer than 252 states was verified by these experiments.**
This directory records the compiler measurements, independent literal checks,
and rejected contractions supporting the main prefix-shift research note.
The delivered initialized prefix machine is maintained by the archive's
top-level constructor and verifier. The `prefix_decrement252.tm` here is an
earlier runtime table under a different register permutation, used as the
control for the rejected 250-state experiment.

All programs use old inherited state labels. A state count excludes the
distinct halt label 254. Labels greater than 254 in experimental tables are
ordinary working states; their numbers are not the state count.

The source pin is ProveIt commit
`43026ff42f0939f09b9e95495248cfadcad38e38`. Imported helpers retain their source
attribution. In particular, omitting the successful-MP dummy truth push is
**already prior work** in pinned `mp_dummy_push_partial_cost.md`. Its exact
204/read 1→132 patch is regenerated here; neither that deletion nor its
8,366-case source guard suite is claimed as new. The new MP0 initializer is
in the sibling `bootstrap/` directory.

## Main finite runtime result

`prefix_decrement.py` implements the eight-row prefix-right decrement change
and checks every one of the 1,925 positive-CD source sites against nine exact
concrete configurations: three primary-register vectors and three gap/spare
settings. All 17,325 checks pass, including the nonzero spare suffix `[2,0,1]`.
The expected effect is a selected-register decrement, gap growth by one,
unchanged spare suffix, and the ordinary source PC successor. Intermediate
visits to dispatcher 96 are followed until exact whole-tape equality holds.

These examples do not prove the unbounded new box contract. Its phase premise,
tape-word proof, and all-call-site symbolic audit are in
`../logic_audit/prefix_decrement_proof.md`,
`../logic_audit/prefix_phase.py`, and the main constructor's verifier. The
new initialized ordering reaches nine zero registers with no spare blocks;
that stronger result belongs to the main delivered machine, not to every
experimental table in this directory.

## Compiler measurements

The native emitter copies source 27's structural-fingerprint reuse method.
It retains unchanged physical subroutines, allocates changed contexts, checks
every guard against the attributed unchanged box contracts, and only then
prunes states not used by those checks or the protected box rows. These are
measured emitted runtime tables, without blank-start proofs unless explicitly
identified by the main archive.

Flags in `native_variants/` are `[AX,MP,DROP,NIP]`:

- AX: omit the initial saved-current-theorem push; GEN binder becomes `D+T`.
- MP: omit the successful-MP dummy truth push.
- DROP: consume the cache while loading it into the current-theorem register.
- NIP: specialize the cache-equals 1 test to two decrements and cleanup.

| Flags | Native DAG nodes | Working states | Passed guards |
|---|---:|---:|---:|
|0000|203|252|8,391|
|0001|205|256|8,382|
|0010|205|254|8,386|
|0011|207|258|8,377|
|0100|203|252|8,366|
|0101|205|256|8,357|
|0110|205|254|8,361|
|0111|207|258|8,352|
|1000|205|257|8,366|
|1001|207|260|8,357|
|1010|207|259|8,361|
|1011|209|262|8,352|
|1100|205|257|8,341|
|1101|207|260|8,332|
|1110|207|259|8,336|
|1111|209|262|8,327|

A direct two-context clone for shifted AX improves its generic native cost
from 257 to 254 states and passes all 8,366 guards; see `direct_ax_variant.py`.
A purported 254-state NIP reuse **fails** at guard 5, the unrelated CI path
`01010`; see `direct_nip/results.json`. Its old states were not free in every
decoder context. It is not a valid NIP implementation.

The whole Wade compiler provides an independent cost control. Across 32,000
grammar trials (four protocol lanes,1,000 seeds, four exponents, two grammar
samplers), the original-AX lanes have best 269-state emitted tables, while
the shifted-AX lanes have best 271-state tables. These costs include the real
62-state dispatcher/engine framework. All winning decoder edges were
independently re-extracted. They do not reconstruct the smaller native Mira
backend.

### Cantor-projection GEN

The new algebraic observation is

`Imp(i,0) = 4 P(i,0) = P(i,i)`.

Because `Imp(i,0)` has a purely propositional proof, either Cantor projection
of a provable current-theorem code can provide any desired generalization
binder. This avoids assuming a global renaming theorem for the code-indexed
native bundle. Full source reasoning and the necessary temporary-cache offset
are in `../logic_audit/projected_gen_theorem.md`.

| Variant | Working states | Native nodes | Passed guards |
|---|---:|---:|---:|
|First projection, clear the other scratch register|261|209|8,350|
|Sum of projections, unrestricted binder proof not claimed here|260|208|8,351|
|Absorb one projection in existing cache-copy arithmetic|260|208|8,307|

The absorbed word is `unpair_T;122;211;162;117;159`. If
`unP(T)=(i,j)` and the old cache is`h`, it produces `All(j,h)` and changes
the temporary cache to`h+i`, leaving the stack and scratch boundary correct.
All 42 binary associations were emitted and all 8,307 guards passed for each.
These are negative compiler measurements despite the useful logical lemma.

## Completed bounded rejection families

Passing literal examples is never promoted to a new box theorem. The word
"conditional" below means that a proposed renamed box interface is assumed
while checking the complete finite source guard suite. A failing guard rules
out that particular claimed interface implementation; these censuses do not
prove a state lower bound. Fuel exhaustion means failure within the declared
bound, not a theorem that the candidate can never return.

| Family | Recipes | Literal checks | Intermediate survivors | Final survivors |
|---|---:|---:|---:|---:|
|Protected-box mixed rows, arbitrary valid spare samples|14,089|1,066,821|1,801 literal|0 conditional affine|
|Protected-box uniform/mixed rows, all-zero spare samples|21,589|3,105,877|2,318 literal|0 conditional affine|
|Reuse one of four prefix scanner states|2,994|1,469,006|34 positive-CD literal|0 complete other-instruction screen|

The first family uses 540 samples. The all-zero family uses 1,260 samples,
with every physical register, primary values up to 5, and zero suffix counts
0,1,2,7,93. Its output suffix must also contain only zero blocks. The prefix
family's 34 survivors all pass 17,325 positive-CD samples;26 also pass 405
mark/INC/zeroDEC box samples. None passes all 6,441 remaining source guards.
The `prefix-decrement-fold-*.tm` files are those **rejected positive-only
survivors**, not smaller consistency machines.

Two late-failing recipes are recorded in the raw mixed-box evidence:
delete 0 into 143 and copy the deleted read 0 action (failure at original
guard 8,160); delete 60 into 120 and copy the deleted read 1 action (failure
at 8,163). These observations suggest where a repair would be needed;
they do not verify a smaller table.

## The rejected 250-state shared scanner

**`../compression/prefix_zero250.tm` is unsafe and must not be presented as a
consistency machine.** From `prefix_decrement252.tm`, remove states 97 and 112,
redirect targets 97→1 and 112→3, and replace 3/read 0 by`0 R131`. This shares the
left scanners, but destroys the zero-decrement control branch.

`shared_scanner_counterexample.py` reconstructs those exact changes and
performs a complete literal root-to-root counterexample:

- Input PC: `1110100100100000100`, selected physical register 0, all nine
  register values zero, no spares, gap 43, dispatcher 96/head 0.
- Correct 252 control:398 steps, zero successor
  `111010010010000011`, gap 43, all registers still zero.
- Rejected 250:486 steps, positive successor
  `1110100100100000101`, gap 44, all registers still zero.

The wrong transfer occurs 209 steps after the common zero-restoration entry
at old 0/head 45. Complete finite one-cell sets, exact hashes, and both traces'
endpoints are in `shared_scanner_counterexample.json`. The arithmetic values
alone would miss the error.

### Local one-state repairs of this rejected table

Each attempted repair adds one fresh working state 255 to the coordinated 250
table. Its two rows have arbitrary write/move/target actions over the 251
working labels and halt, giving 1,008 choices per row. The C++ search uses
lazy assignment and conflict-directed backtracking; full assignments whose
unread row cannot affect the witnessed failure are eliminated together.
Its exact repeated-configuration check compares the whole finite bitset.
The step bound is 10,000; tape positions outside its 2,048-cell window reject
that bounded trial.

| Modified incoming row | Full assignments covered | Search nodes | Literal checks | Survivors |
|---|---:|---:|---:|---:|
|0/read 0, four write/move choices into 255|4,064,256|723,356|723,650|0|
|75/read 0, four write/move choices into 255|4,064,256|1,526,687|1,547,495|0|
|109/read 0 fixed to`0 R255`, both fresh rows arbitrary|1,016,064|8,065|8,065|0|

The first two families use 27 no-spare zero-restoration samples and allow
correct zero control with gap growth 0,1,or 2. Original 252 continuations pass
every control. The last family tests a concrete lookahead mechanism: after
the shifter stops at 00, the next cell is 1 for marked positiveDEC and 0 for
whole-file zeroDEC orINC. Its 81 tail samples cover all three instruction
types. All 81 original full-root controls are checked during export, and
the native runner rechecks the 54 original positive/INC continuations.
Zero samples start from the rejected table's full-file-shift boundary and
require the correct source zero successor. No candidate passes even the
first required zero sample. The smaller fixed-positive-action sweep is
separately recorded in `prefix_tail_lookahead_results.json`.

### Final repair using two existing rows

The positive prefix excursion never reads 1 in state 131. A final bounded
check therefore freed 131/read 1 together with either 0/read 0 or 75/read 0,
while preserving 131/read 0 as `0 R95` and every other row. These families
allocate no new state. Each free row has 1,004 write/move/target choices
(250 working targets plus halt), so each family covers 1,008,016 full
assignments.

| Free rows | Search nodes | Literal checks | Survivors |
|---|---:|---:|---:|
|0/read 0 and 131/read 1|4,017|4,017|0|
|75/read 0 and 131/read 1|4,017|4,238|0|

Both searches use the same 27 exact no-spare zero-continuation cases, accept
the correct zero successor with gap growth 0, 1, or 2, and first verify all
27 original 252 controls. They use the same 10,000-step and 2,048-cell bounds
as the fresh-state searches. Their negative result is limited to these
specific two-row families and finite continuation requirements. Evidence
is in `zero_existing_pair.cpp` and the two `zero_existing_pair*/summary.json`
files; the input table and cases are reused from `zero_newstate/`.

## Reproduction

Run these commands from the archive root with assertions enabled (do not use
Python's `-O`). Paths are relative to the script location, so no original
workspace path is required. The curated pinned `source/` subtree and sibling
`bootstrap/`, `compression/`, and `logic_audit/` directories are dependencies.

Fast controls and selected compiler measurements:

```sh
python3 -B redesign/mp_protocol_runtime.py
python3 -B redesign/prefix_decrement.py
python3 -B redesign/shared_scanner_counterexample.py
python3 -B redesign/native_protocol_variants.py
python3 -B redesign/projected_gen_compile.py
python3 -B redesign/absorbed_gen_compile.py
```

The full Wade grammar control and bounded fold censuses are optional:

```sh
python3 -B redesign/destructive_axiom_compile.py --output redesign/destructive_compiled --seeds 1000
python3 -B redesign/box_mixed_search.py --output redesign/box_mixed_results.json --seconds 300
python3 -B redesign/zero_spare_box_search.py
python3 -B redesign/prefix_decrement_folds.py
python3 -B redesign/prefix_fold_followup.py
```

The one-state local repair searches require a C++17 compiler:

```sh
python3 -B redesign/export_zero_newstate.py
python3 -B redesign/export_tail_newstate.py
g++ -O3 -std=c++17 redesign/zero_newstate.cpp -o redesign/zero_newstate_search
redesign/zero_newstate_search redesign/zero_newstate
redesign/zero_newstate_search redesign/zero_newstate75 75
redesign/zero_newstate_search redesign/tail_newstate 109
```

The final two-existing-row checks use those same exported zero cases:

```sh
mkdir -p redesign/zero_existing_pair0 redesign/zero_existing_pair75
g++ -O3 -std=c++17 redesign/zero_existing_pair.cpp -o redesign/zero_existing_pair_search
redesign/zero_existing_pair_search redesign/zero_newstate redesign/zero_existing_pair0 0
redesign/zero_existing_pair_search redesign/zero_newstate redesign/zero_existing_pair75 75
```

`results-summary.json` gives a compact machine-readable index. The raw result
files preserve individual failures and experimental tables so that a future
coordinated repair can start from a concrete witnessed obstruction.
