# Independent encoding audit of the delivered 245-state machine

**Verdict: PASS for allocation, renumbering, closed-atom reassociation and all
special-entry routing equations. No defect found in this scope.**

Audited archive: `audit245/extracted/zfc245-proof-20261018`.
Canonical table SHA-256:
`17f4d430747c4a0cd580dc2cc13ea06a74ce7f51f12be4c2d12f6a646691dd13`.
The independent checker is `audit245_encoding.py`; its detailed certificate is
`audit245_encoding.json`. It imports none of the archive's producer/checker
code and does not rerun search.

## Exact state accounting

The baseline has119 framework states and127 pure grammar states. The final
construction has117 framework states and128 grammar states: **245 working
states**, all with both binary rows, plus a separate halt. All initialization
states are included; no unreachable grammar helper is silently omitted.

The two removed *framework roles* are the old scanner74 and old router177.
The router is represented by a charged grammar rule instead. Thus absorbing177
is not, by itself, a free state reduction:117+128=245 is the relevant complete
ledger. Equivalently, before scanner shortening the reclassified framework and
new grammar total118+128=246; the scanner contraction supplies the net−1.
Achieving zero-run6 inside that128-rule grammar budget is what makes it possible.

Labels are reused. In the literal final old-label machine:

-74 is the new grammar helper `([132],[16])`;
-177 is a large grammar phrase, with rows0R165 and1R185;
-208 is another grammar phrase, with rows0R199 and1R190;
-the only baseline working label absent is247; no new numeric label is added.

There are43 removed old grammar words and44 new words, net+1. The old semantic
word attached to208 is removed, although numeric208 remains. There are104
changed retained rows versus the pinned baseline, so the explanatory handful
of edits is not a replacement for the complete delivered table.

I reconstructed the allocation from the grammar and available labels, then
reconstructed every one of490 original-label rows from the pinned baseline,
routing map and grammar. The result equals the delivered table exactly.
Canonicalization is independently checked on every row: old95→0, old96→88,
old254→245; working states are exactly0..244, and halt245 has no rows. Both
renumbering JSON files agree with the independently constructed bijection.

## Reassociation is restricted to closed atoms

I freshly parsed the6,459-node original `Prog254.v`, checked it byte-for-byte
against the pinned repository copy, and reconstructed its full6,460-leaf tree.
The grammar's original AST equals this tree exactly.

For each AST, the checker computes its outward break/continue bounds. All44
semantic atoms have bounds(0,0). At every original pure-sequence boundary,
both children independently have bounds(0,0). The final grammar concatenates
exactly the same semantic words; no logical-schema or AX-word override occurs.

The checker then constructs a normal form that flattens a binary node **only
when both children are closed**, retaining every other control node and every
instruction/argument. The complete old and new normal forms agree. This is a
closed-sequence reassociation witness, not a claim that arbitrary trees with
the same ordered leaves are equivalent. Separately, all6,460 ordered leaves
and arguments agree. The final source has leading-zero length3, maximum zero
run6 and maximum path depth51.

The atom orientation masks are independently rederived from the original
literal grammar edges, rather than trusted as unexplained metadata. All60
final terminal-child uses respect those masks. Every one of128 grammar rules
is reachable from a retained entry root or an explicitly routed entry.

## All special-entry routing equations

An exhaustive scan of baseline edges finds exactly11 left-moving external
entries into the grammar or old177. These are exactly the11 routing groups
provided, each checked for both possible preceding tape bits:22 cases total.
There is no omitted left-entry group.

For each case the checker executes the caller row and its one or two
transparent decoder rows in both literal tables. The inspected bits are only
the preceding cell and, where needed, the just-written caller cell. Both
traces preserve those cells, take the same number of steps, finish at the same
head offset, and reach the same numeric endpoint in this delivered allocation.
Thus the equations do not assume an unproved value for an exterior tape bit.
The exact traces and semantic endpoints are recorded in the JSON certificate.

### The177 role

The only original incoming edges to old177 are153/read1 and159/read0. Both
now enter grammar state157. Its literal rows are0R175 and1R207, precisely the
old router's rows. After the following transparent row, the four required
projections are:

| Caller | preceding bit | inspected prefix | endpoint |
|---|---:|---|---:|
|153/read1|0|01|105|
|153/read1|1|11|231|
|159/read0|0|00|113|
|159/read0|1|10|213|

All four are verified in the literal tables. Numeric177's later reuse does not
reintroduce the eliminated special framework role.

### The218/read0 repair and178 rotation

The old word178 has association`([23],([24],[206]))`. The new association is
`([16],[206])`, because16 is`([23],[24])`. This removes the old word208, but
on its own it would break the folded218/read0 entry into old154.

The delivered repair changes218/read0 from0L154 to0L86. Its two required
projections hold literally:

-86→0 98→0 23, so prefix00 reaches23;
-86→1 99→0 105, so prefix10 reaches105.

The new98 has rows0R23 and1R74; helper74 has rows0R132 and1R16. This changes
98 from`(([23],[132]),[16])` to`([23],([132],[16]))`, preserving its closed
semantic word. State99 remains`([105],[114])`. Thus the repair both restores
218's two contexts and changes the left-spine structure needed for zero-run6.
Other charged reassociations are still needed for the global128-rule budget
and zero-run bound; these local edits alone are not the delivered construction.

## Bootstrap equations and limits of this audit

All54 supplied bootstrap row equations agree with both the original grammar
children and the final literal rows. The scanner edit is exactly58/read0→0L84;
its old74 scanner role is absent. This audit does **not** infer full scanner
safety merely from zero-run6, nor use finite testing as an unbounded runtime
proof. Scanner transient contexts, register-macro induction, residual-pointer
composition, exact blank initialization and the consistency calibration are
separate audits assigned to the other workers.

The result here establishes the finite encoding/routing premises of that
larger argument and verifies that the advertised net one-state saving is fully
charged and realized in the exact delivered table.
