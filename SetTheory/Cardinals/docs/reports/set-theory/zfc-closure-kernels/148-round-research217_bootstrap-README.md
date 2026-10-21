# Initialized 217-state core and a fresh bootstrap discriminator

## Verified result, not a blank-started candidate

Starting from the newly audited K218 native table, remove state 301 and apply the established fold:

- 87/0 becomes 0 R 88.
- 88/0 becomes 0 L 51.
- 51/0 becomes 0 R 122.

The parent SHA256 is `2dfaba6da09b78291e534777cd30c5f0d68bd84faa670e868e779c396aeb308f`.
The exact resulting `initialized217.native.tm` SHA256 is
`c3d90a672481086329d8ed93da24a885d80a553ae6298b3a6444bea0fd5cee53`.
It has 217 working states and 434 rows. The unchanged new source SHA256 is
`b0169f2d477d0584ac70f9bdb79c3a78ef2bc700d080b3cd80976210235b80d9`.

The owned mathematical kernel freshly proves all 6,167 primitive guards,
using 1,515,310 symbolic rules and every one of the 434 rows. The minimum
constant duration is 12. Registers, extra gap and nonempty finite spare lists
are arbitrary. This is an initialized-core theorem only: its known 85-step
blank failure has not been repaired or reclassified as a valid seed.

## New-source tag theorem

A conservative observer was installed in the owned symbolic checker. It
never samples an arbitrary run length or list tail. When enough bits are not
fixed for all natural valuations, it would explicitly record an unknown
window. There were no unknown windows.

Across the complete primitive proofs it saw 4,795 state-51/read-0 events:

- 4,747 have right neighbor 1.
- The remaining 48 have right neighbor 0 and left-six masks exactly
  `{3,6,15,35,38,47}`.

Mask bit 0 is at offset -6 and mask bit 5 at offset -1. The right-zero events
occur at exactly the eight CD5 source leaves with indices
4567, 4572, 4585, 4590, 4599, 4604, 4708 and 4713. Each occurs three times in
each of its two symbolic guards, including later engine passes. Thus this
is not merely a decoder-prefix sample or an inherited old-source cover.

The new K218 blank startup was also independently replayed to its exact
312,909-step clean root. It has the same five exceptional scanner visits at
steps 79, 160, 306, 471 and 1496, with left-six masks
`{0,2,21,26,28}`. The first four complete tapes agree with the corresponding
old219 snapshots. The fifth does not: its relative cell -25 is zero rather
than one. The freshly generated new-source snapshot is used here.

The two mask sets are disjoint. An equivalent short decision procedure is:

1. If the nearest left one is at distance 1, 3 or 4, choose the decoder role.
2. If it is at distance 2, or no one occurs in the first five cells, choose
   the bootstrap role.
3. At distance 5, inspect the sixth cell: one selects decoder, zero selects
   bootstrap.

This gives a concrete finite decision rule, not a zero-state implementation.

## Exact repair obligation

Let the state-51 head be h, scanning zero. For right neighbor zero:

- The bootstrap role must reproduce the old local effect: write one at h+1
  and continue in state 1 at h, leaving everything else unchanged.
- The decoder role must reproduce the folded effect: leave the tape
  unchanged and continue in state 137 at h.

For right neighbor one, old and folded paths agree: clear that cell and
continue in state 1 at h. These contracts must be established before a
helper can be composed into the full runtime theorem. Separation alone
proves no repair.

## Existing-path inspection and obstruction

Only seventeen concrete existing left-moving entry paths were inspected,
not arbitrary row mutations. The complete fresh five boot tapes and eight
new-source decoder prefixes were used.

- Entries 1,2,3,5,9,15,23,34,50 run the global sentinel search. They either
  reach dispatcher 84 without the required local effect, or enter an exact
  outward blank ray on an early bootstrap tape. They do not implement a
  restoring local classifier as-is.
- Entries 40 and 54 enter the destructive state-4/state-6 routine before
  reading the hard distinguishing bit.
- Entries 13,62,63,76,152,157 inspect at most three left cells before their
  first write on the hard pair: boot step 306 versus decoder site 4567.
  Their entire traces up to that write are identical for the pair. They
  therefore cannot perform the required six-bit read-only discrimination.
  This observation does not exclude a future destructive-then-restoring
  multi-row construction.

A tempting route through state 76 reaches state 35 at h+1 on the first boot
exception. Changing 35/0 to 1 L 1 would give the desired effect there, but
that row is not a free bootstrap helper: on the valid all-zero-register
CI0 frame at source address 0110, the change returns an incorrect complete
frame after 36 steps. The unmodified initialized217 performs the required
operation in 658 steps. This is an exact generic-contract obstruction to
that naive repair, not a claim about that patched machine's blank semantics.

The separate encoding lane also screened the exact 88/301 two-cell and
three-cell marker selectors with unchanged helper rows. Those results are
not duplicated here.

## Reproduction and limits

- `prove_initialized_and_tags.py` and `INITIALIZED217_TAG_PROOF.json`:
  full unbounded initialized runtime proof plus conservative tag observer.
- `INITIALIZED217_TAG_CASES.json`: complete ordered guard census, SHA256
  `efec27d6d7065d337b331ed3556c76e20d02dadd17b7c817e726b65a9f5507fc`.
- `bind_new_contexts.py` and `NEW_CONTEXT_BINDING.json`: exact fresh boot
  snapshots and every new source read-only decoder prefix.
- `inspect_scanner_paths.py` and `SCANNER_PATH_INSPECTION.json`: the narrowly
  scoped literal helper-path inspection.
- `STATE35_ONE_WRITE_OBSTRUCTION.json`: complete finite contract witness.

All executed code was owned analysis code. Received tables and source files
were read as data only. This work proves neither a blank-started 217-state
construction nor any state lower bound. It identifies a newly certified
local invariant and the concrete restoration problem a successful reuse
must solve.

## Subsequent source-side check

`CD5_SOURCE_FINDINGS.md` identifies all eight conflicting decrements as four
shared equality calls (two AX gates, NIP and MP), transports the existing
seeded invariant to the exact new source, and prices four small guarded
rewrites. The known NIP variants cost raw220,218,220 states and retain the
state301 role. A new R3=0 scratch-register rewrite removes301 but costs raw221.
No branch was discarded by assuming consistency or cache != 1.

## Four-bit crossover strengthening

The separate crossover30 subdirectory now contains a fresh all-natural217
runtime proof on the closed30-leaf reassociation:6167 cases,1,515,251 rules,
all434 rows, zero unknown scanner windows. Its nearest-four-bit runtime
masks{1,3,9,11} are disjoint from exact startup masks{0,5,6,7}. The four-row
218 parent still reaches the same clean seed in312909 blank steps. An
existing-entry six-cell helper pilot is negative within its bounded local
scope; no bootstrap repair follows merely from the disjoint masks.

## Transfer-free equality producer inspection

Three equality comparisons can directly targetR3 with no extra transfer:
secondAX, NIP andMP, using the same symmetric E(3,5) macro. The firstAX
producer has a genuine local R3/R5 live-range conflict; its directCI6→CI3
rename diverges for positive selectorc. A mixed E(6,5)/E(3,5) proposal adds
no leaves but splits equality sharing and introduces unsupported right-child
CD5. No allocation was attempted. See EQUALITY_PRODUCER_FINDINGS.md and
EQUALITY_PRODUCER_LIVENESS.json for exact edits, guards and scope.

A later single combined pilot appended the already-existingR6→R3 transfer
once after the firstAX producer, allowing all four calls to shareE(3,5).
It has209 source nodes/4747 leaves. With provisional unprovedrightCD5=1R45,
the emitted table counts223 states and has one role-binding discrepancy;
therefore no focused/full runtime proof was pursued. This is a scoped raw
allocation result, not an impossibility claim about rightCD5.
