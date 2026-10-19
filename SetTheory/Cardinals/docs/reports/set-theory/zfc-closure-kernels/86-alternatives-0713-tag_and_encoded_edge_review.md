# Independent review: tag-bit checking and native edge traversal

Date: 2026-10-18. Artifacts in `../architectures`: `tag_edge.py`,
`native_edge_step.py`, `encoded_native_edge.py`, and their literal tables.
Hashes and executable results are in `tag_native_edge_independent_audit.json`
and `encoded_native_edge_independent_audit.json`.

## Verdict

The 16-state tag checker, its independently constructed 15-state restricted
quotient, the older 67-state four-entry edge, and the newer 68-state single-entry
fixed-header edge all satisfy the valid-frame contracts below. The 68-state
machine genuinely reads its own mode and preserves a fixed-size header; no
external branch-bit oracle is used inside that component. It still does not
produce/update that header from template queries, preserve/advance a template
path, validate a whole arena/proof, or enumerate candidate certificates.

**An explicit inherited boundary condition is essential:** the tape cell just
to the left of the counter's leftmost one must be zero. The copier alone does
not need this condition, but the locator uses that cell to recognize its last
counter unit. A one there is interpreted as an extra unit and can select the
wrong record. Independent tests first exposed this distinction; valid-frame
composition tests then enforced the locator's actual precondition. Arbitrary
left exterior may start one cell further left.

## Tag checker: universal contract and one-state quotient

For branch b and expected bit e in {0,1}, define a four-bit acceptance mask
`m=sum(2^t for 0<=t<4 with ((t>>b)&1)=e)`. After restoring the erased first one
of tag field `1^(t+1)0`, the machine reads the remaining t ones and its delimiter.
Its test state after k such ones holds mask `m>>k`. Reading another one shifts
again; if the mask becomes zero, rejection is correct because no later allowed
tag remains. At the delimiter, success occurs exactly when the low mask bit
is one. Thus for every valid tag 0<=t<4 it accepts exactly the required observed
bit. No formula decoding or arithmetic oracle is hidden here.

On success with b=0 it reaches the first left-reference one directly. With
b=1 it scans the nonempty left-reference field to its delimiter and reaches
the first right-reference one. It erases that first one, moves left onto the
preceding zero delimiter, and returns right onto the erased cell. It restores
the tag marker and changes no other tape cell. On a valid-frame mismatch it
reaches the reject port with only the original tag marker restored; it has not
modified a child field. No fixed reject head is claimed.

`mark_child` therefore reads only one, and `return_right` only zero. Identify
return_right with mark_child, keep its one row as `(0,L,self)`, and replace its
zero row by `(0,R,RETURN)`. All old rows project identically except the two
excluded pairs `(mark_child,0)` and `(return_right,1)`, which the preceding
invariant excludes. Literal-step induction proves identical valid traces and
full-tape exits. The quotient has 15 working states, including reject, and
30 rows; the separate return is 15. The reviewed table is
`tag_edge_15_verified_fold.tm` in this verification directory, SHA-256
`4ccce8db281c262260406621f7a0d56cb3879b302ba48d628cc068c036cb179c`.

This standalone fold is **not another saving on the 68-state composition**:
that table already removes the return adapter by fusing child entry with the
biased copier.

## Older four-entry 67-state composition

On a valid arena of m records, each with tag t<=3 and references in [0,m), let
selected record s have its first tag one erased. The counter is a single one,
its left neighbor is zero, and the counter-to-anchor gap has at least r+2 zeros
for the selected reference r. The four entry ports explicitly carry b,e.

The tag theorem selects the marked reference field. The original 30-state
copier restores that field and writes counter `1^(r+1)`, returning on its
rightmost one. The reset routine crosses the remaining gap and anchor `10`,
erases the first tag one of record 0, and enters the locator's backwards return
scan. That scan reaches the same counter; the locator moves the marker from
record 0 to record r and reduces the counter back to its leftmost one. The last
adapter moves left from locator's marker+1 exit to the erased marker itself.
Thus on success only the original selected-record marker moves to record r.
The counter, gap, anchor, all fields and exterior are unchanged. All component
scans terminate under their already proved frame bounds. The 67-state count
includes all five reset/head adapters and one shared reject sink.

## Single-entry 68-state fixed-header theorem

Encode each record by unary tag length t+1, left-reference length L+3 and
right-reference length R+3, separated by zeros. All references are in [0,m).
Let k=1+2b+e. The header after the counter gap is exactly

`1^k 0 1^(5-k) 0`, with k in {1,2,3,4}.

It has fixed length seven; both one blocks are nonempty. The initial counter
is one at c with zero at c-1, and the gap g satisfies g>=r+2 for the selected
reference r. The only arena marker is the erased first tag one of the selected
record. Enter the single `fetch` state at that cell.

1. **Mode acquisition.** Fetch steps left past the marker's preceding delimiter
   before beginning the backwards field scan. Thus it does not confuse the
   marker's temporary zero with the counter gap. All earlier field/header
   delimiters are isolated zeros. The first double zero encountered is the
   gap. The rightward scan finds the first header one, and four counting states
   distinguish k=1,2,3,4 at its delimiter. They select exactly b,e as encoded.
   Every tape bit remains unchanged.
2. **Find selected tag.** The four reused tag-entry states and four associated
   one-scan states retain that mode while passing the nonempty padding field
   and earlier arena fields. They stop at the unique erased first tag cell.
   The original tag-mask theorem then checks the selected observation and
   restores the marker.
3. **Fused reference-copy entry.** On tag success, the chosen reference field's
   first cell is still one. Instead of erasing it and then restoring it, the
   changed child-start transition preserves it, moves right, and enters the
   biased copier's first erasure state. At that point the source's first cell
   is already restored, the next two cells are guaranteed one (length r+3),
   and the counter is still its single one. This is precisely the proved
   copier invariant immediately after its omitted initial-cell adapter.
4. **Copy across header padding.** The variable-anchor copier treats the first
   header block as an arbitrary positive anchor, then scans the second block
   as one ordinary unmarked nonempty field before the arena. Its two-zero
   marker detection remains unique. It restores the source and writes the
   counter of r+1 ones, leaving at least two gap zeros.
5. **Reset and locate.** The five reset states pass the first header block and
   then the padding block, erasing the first tag one of arena record 0. The
   backwards locator scan returns through those nonempty fields to the counter.
   The locator's anchor states were explicitly extended to pass additional
   anchor ones. Its field-search phases treat the padding as an unchanged
   nonempty prefix field before record 0. Its three-field advances begin only
   at the actual erased record marker, so the padding does not change record
   indexing. The earlier locator induction therefore applies unchanged after
   this harmless prefix extension. It selects record r, resets the counter
   to one, and the final left adapter returns onto the new erased marker.

Every segment has a finite bound supplied by the validated field lengths,
index range and remaining counter gap. Composition proves that a matching tag
returns with **only the arena marker moved** to record r, at the correct head.
A mismatching valid tag reaches the reject port with its old marker restored
and no other tape changes. Header bits and extent never change. A succeeding
call is valid again if its header mode and gap capacity fit the new selected
reference; the machine does not itself update the mode.

The exact charged partition is 14 tag/child-start states, 17 biased-copy states,
17 locator states, five reset states, one head-return state, 13 mode-fetch/search
states, and one shared reject =68. The separate return is 68; there are 136
rows. Table SHA-256:
`87babb7eedeb7ed26c39b93d83a4fd09690959b831b741260ff4d92b35971721`.

## Executable checks and remaining boundary

Independent sparse simulations and full-tape comparisons passed:

- 1,152 tag cases, with exact projected execution of the 15-state quotient;
- 1,120 older 67-state edge cases at minimum selected-reference gap;
- 2,112 calls to the 68-state edge, including 1,152 successes, translated
  origins, minimum gap, arbitrary safe exterior bits, and 192 successive calls
  reusing an unchanged header without resetting counter, marker or fields.

All 67 operational states of the 68-state table were exercised. Maximum
independently checked call length was 3,652 steps. No Python callback supplies
the branch/observation during these single-entry table executions; the header
is genuinely read by the literal transition table. Preparing or updating that
header remains a separate unimplemented routine, not a free operation.

The nonhalting reject sink and possible malformed-input scans are still outside
a fair candidate rejection protocol. Integrating this edge with the oracle
must preserve requested path information (the earlier destructive pipeline has
proved collisions), generate/retain each expected observation, update the mode
header, terminate each complete path, handle virtual node zero, validate all
indices and repeated parameters, and implement complete proof search/startup.
None of those operations or their state costs is established by this review.

No producer file, shared checkout, external repository, or user computer was
modified during this review.
