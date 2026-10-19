# Independent review: reverse path copier and read guards

Date: 2026-10-18. Exact table hash:
`b47f336ad5e5ce8a1d9ffb4277a738c256b820c21b0ada99b3b4e63e41936a2b`.

## Verdict and exact contract

The 19-state literal reverse copier is correct on its prepared frames. Its
four forced-one states are IDs 1,2,5,9 (payload1, payload2, mark_previous0,
mark_previous1), and its proved forced-zero states are IDs 0,13 (restore,
append). A conservative complete guard map, exact labels and proof reasons
are in `reverse_path_copy_19_guards_reviewed.json`. The other states, including
reject, are conservatively assigned both symbols. There are 18 operational
states plus reject, 38 rows and separate return 19.

Let bits be b0..b(n-1), each in {0,1}. At c put frontier1, followed by g>=n+2
zeros, sentinel `111110`, and the fields `1^(b+3)0` in the given order. Erase
the final one of the last field, or of the sentinel if n=0. Enter restore at
that erased cell. Every other tape cell, including the adjacent left exterior,
can be arbitrary.

The machine restores the entire source and sentinel. It overwrites c..c+n-1
with b(n-1)..b0, places frontier1 at c+n, and returns at c+n-1. Every other
cell is unchanged. It never reads left of c or beyond the initial marker's
following delimiter. For n=0 the returned head is c-1 but that cell is not read.

## Universal induction

After k copied bits, 0<=k<=n, the output prefix c..c+k-1 contains the last k
input bits in reverse order, frontier1 is at c+k, and the remaining gap has
g-k>=2 zeros. Exactly one source one is erased: the final one of the last
uncopied branch, or the final sentinel one when k=n. All other source cells,
including all already copied later branch fields, are restored. Entry restore
is at that erased cell.

For k<n, restoring the marker and taking the two payload steps reads two
preceding ones, since each branch field has length at least three. A length-3
field next presents a zero separator at optional, selecting bit0. A length-4
field presents one there and zero at long_test, selecting bit1. In either case
mark_previous is positioned on the final one of the preceding branch or the
sentinel; that one exists and has not been changed. It erases it and scans left
from the surviving one prefix. All intermediate delimiters are isolated zeros,
so the backwards two-zero detector identifies the gap. It scans left to the
rightmost frontier1, replaces it by the recovered bit, and appends frontier1
at the next gap cell. This cell is zero and at least two gap zeros remain.

The forward scan crosses the gap, sentinel, and earlier intact source fields.
Its first pair of consecutive zeros is precisely the erased final one followed
by its field delimiter. It moves back to that marker in state restore. This
establishes k+1, including complete tape preservation.

For k=n, restore is at the sentinel's final one. After restoring it, payload1
and payload2 read its preceding ones, and optional and long_test both read one.
Only the five-one sentinel has this pattern; branch fields have length three
or four. The machine is then immediately left of the sentinel, in the remaining
zero gap. finish_gap scans left to frontier1 and returns one cell left of it.
Thus all n branch iterations and the final sentinel phase terminate. The
finite scan bounds are the explicit gap, field and frontier delimiters; no
external fuel or blank region is hidden in the proof.

The four forced-one claims follow directly: payload1/2 always inspect those
preceding source/sentinel ones; mark_previous0/1 always inspect the unmodified
last one of an existing preceding field/sentinel. Restore always reads the
unique erased marker, and append always reads the next still-blank gap cell.
These facts hold on every internal visit, not only initial entries.

## Mirrored oracle interface

The returned head c+n-1 reads b0,b1,... when moving left, so a left-moving
mirror of the template oracle reads the path in root-first order. The source
path remains intact and can support a later regeneration protocol; that
protocol and its states are not implemented merely by this local copy.
After the n path cells, the mirrored oracle's three leaf emitters read cells
c-1,c-2,c-3. The copier itself permits these to contain arbitrary bits. **To
assign the mirrored leaf emitters forced-zero guards for packing, the combined
caller must reserve all three cells as zero.** Ordinary oracle correctness
permits arbitrary emitter-input bits, but that broader contract is insufficient
for the proposed symbol-partition packing. No left-padding condition can be
inferred merely from the copier's success.

Initial construction of the unary source fields, erasing its initial final-one
marker, choosing a genuine leaf path, restoring any output workspace and
routing each return remain charged caller operations. The reject sink is not
a terminating malformed-candidate rejection protocol.

## Independent evidence

`audit_reverse_path_copy.py` independently builds frames, parses the emitted
table, and checks all tape cells and the exact return head. It passed 1,065
cases, including empty paths, all paths through length seven, longer random
paths, minimum capacity, translated origins and arbitrary adjacent exterior
bits. Every selected forced-read guard was checked during these runs;
maximum length was 12,271 steps. The finite checks supplement the induction.
No producer file or shared source was modified.
