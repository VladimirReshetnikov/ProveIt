# Independent review: 30-state marked unary copier

Date: 2026-10-18. Source: `../native_copier/marked_unary_copy.py`, SHA-256
`446e71954bd3027fa9917327939298c597f37ad6adfe352c3a095a08bbf20c33`.
Literal table: `marked_unary_copy_30.tm`, SHA-256
`50c006e5bda4dee7eb2530c4f33e56ce3d98798a53fe8cf12d66b34a811aef72`.

## Verdict

**The stated prepared-frame contract is correct.** The two-zero moving marker,
capacity condition, whole-tape preservation and return head all admit the
universal induction below. No hidden separator or extra blank region is needed
beyond the explicitly stated gap of at least v+2 zeros, anchor `10`, nonempty
preceding unary fields, and the source's terminating zero.

The exact table has 30 working states: 29 operational states and one nonhalting
reject state, with separate return label 30 and 60 transition rows. This is a
component, not a complete proof verifier, fair enumerator or blank-tape machine.

## Exact theorem

Let c be the initial counter coordinate, v>=0 the selected field's value,
g>=v+2, and a=c+g+1 the anchor coordinate. The counter is the single one at c;
positions c+1 through a-1 are zero; positions a,a+1 are `10`. Starting at a+2,
there are finitely many earlier fields, each a nonempty one block followed by
one zero. Let s be the next field start. The selected field has value v:
positions s through s+v would normally be one, followed by a zero at s+v+1.
Initially exactly its first cell s is erased. Start in state `init` at head s.
All tape cells outside [c,s+v+1] can be arbitrary. In particular no blank left
exterior is required, and later fields need not even be well-formed for this
local theorem, because they are never inspected.

Then the machine terminates in return label 30 at head c+v. It restores the
one at s and writes ones at c through c+v. Every other tape cell equals its
initial value. Every scanned position lies in [c,s+v+1]. Thus both the entire
field stream and arbitrary exterior contents are preserved, except the intended
restoration of the input marker and the new counter copy.

## Backward-scan sublemma

Each `mode_ones/mode_zero/mode_gap` triple is used only from a restored one
prefix lying to the left of any moving marker. In that scanned prefix, all
field and anchor separators are isolated zeros, since each earlier field is
nonempty. Reading a zero moves to `mode_zero`, whose next zero recognizes the
pair of zeros in the counter gap. It then scans left across the remaining gap
until the rightmost counter one and moves right into its continuation. The
counter one is a finite left bound, and it is never crossed. This scan makes
no tape changes. Its only needed delimiter assumption is at least two gap
zeros; no delimiter elsewhere is silently introduced.

## Boundary cases

- **v=0:** `init` restores s, and `init_one` immediately sees the field delimiter.
  It moves left to `done_ones`. The backward-scan sublemma finds the original
  counter, and `return_left` reads the first gap zero and returns to c. Nothing
  is added to the counter.
- **v=1:** after restoring s, `init_one` passes the second source one;
  `init_two` sees the field delimiter. The `finish_one` backward scan reaches
  c, `add_finish` writes one at c+1, and `return_left` returns there from the
  next zero. The entire field is already restored. The stated g>=3 certainly
  supplies the needed zero; a weaker special-case bound is unnecessary.
- **v=2:** initialization restores s and erases s+1,s+2. The `two` backward
  scan plus `add_two/add_loop` grows the counter by exactly two ones. Forward
  search finds the pair of source zeros and immediately sees the field
  delimiter; it restores both zeros and finishes. This is also the base case
  of the invariant below, with no ordinary loop iterations.

## General moving-marker induction

For v>=2, consider each entry to `gap_right` after k units have been copied,
where 2<=k<=v. Its invariant is:

1. The counter contains exactly the contiguous ones c through c+k.
2. Its remaining gap has g-k>=2 zeros, followed by unchanged anchor `10`.
3. The source's only temporary zeros are s+k-1 and s+k; every source cell to
   their left is restored, and cells s+k+1 through s+v remain one.
4. All other cells are unchanged. The head is c+k+1.

Initialization establishes k=2: `init` restores s; `init_two/mark_first` erase
s+2 and s+1; the `two` scan runs from s, left of the new pair, and the two
counter-writing states append precisely two ones. Since g>=v+2>=4, at least
two gap zeros remain.

From the invariant, `gap_right` traverses the finite gap to the anchor.
`after_anchor` checks its zero separator. `find_first/find_ones` cross all
earlier nonempty fields and the restored source prefix. The first zero of the
moving pair is encountered by `find_ones`; the second is encountered by
`find_first`, which moves right into `next_source` at s+k+1. No earlier field
can imitate this two-zero pattern.

If k<v, that cell is one. The machine erases it, leaves the old right marker
zero unchanged, restores the old left marker to one, and enters `loop_ones`
strictly to the left of the new marker pair. Its backward scan is therefore
unambiguous and finds the rightmost counter one. `add_loop` appends one, and
enters `gap_right` at c+k+2. The new gap has g-(k+1)>=2 zeros, establishing the
invariant for k+1.

If k=v, `next_source` sees the selected field's terminating zero. It moves left
and restores both marker zeros, then enters `done_ones` at s+v-2. The backward
scan finds the counter's rightmost one c+v, and `return_left` reads the first
remaining gap zero and returns to c+v. All source cells are now restored.
Every scan has the stated finite bounds. Exactly v-2 advancing iterations
occur, so termination follows without a fuel assumption.

The g>=v+2 capacity condition is substantive. For example, v=2 with only g=3
leaves a single gap zero after the two counter increments; the final backward
scan then crosses the counter instead of recognizing its boundary and can
wander indefinitely on a blank left exterior. No caller may silently omit the
capacity check/reservation.

## Integration obligations

The input marker is consumed by restoration. Subsequent calls must establish
whatever new marked field and single-one destination they require. The helper
has no total reject-and-restart semantics for malformed frames; wrong entries,
missing anchors, capacity exhaustion and extra marker zeros remain outside its
contract. A fair proof-search runtime must validate or generate valid frames,
or separately guarantee bounded failure handling.

For composition with the reviewed locator: after locating record i from a
counter of i+1 ones, its leftmost one is the potential copier destination and
the gap has grown from g to g+i. Therefore a field value v fits precisely when
v+2<=g+i. Valid backward references may imply this bound, but the implication
must be proved for the actual indexing convention. A tag value 3 at i=0 needs
g>=5; the earlier pipeline default g=4 does not suffice. Also the locator exits
at marker+1, whereas this copier enters at marker. An adapter or changed entry
must be included in both the proof and the state count. No particular combined
table is certified by this observation.

## Independent executable evidence

`audit_marked_unary_copy.py` parses the emitted table, compares it against the
compiler, independently constructs the frames and independently simulates the
literal table. It passed 1,260 complete-tape checks, including 165 cases each
for v=0,1,2, minimum capacity g=v+2, arbitrary preceding fields, translated
origins, and arbitrary immediately adjacent exterior bits. All 29 operational
states and 47 valid transition rows were exercised; the other totalized rows
are excluded by the proved precondition. Maximum checked run length was
38,392 steps. Results are in `marked_unary_copy_independent_audit.json` and
`.log`. The producer's completed main suite separately reports 5,756 passes
and maximum 297,763 steps. These finite checks supplement the induction above.

No producer file, shared checkout, external repository, or user computer was
modified by this review.
