# Audit of expanded macro entries

The corrected copy-H remainder entry is **native state 179**, not state 30.
The ordinary H/GDH pair-recognition rules agree with the literal fixed rows
after that correction. The deeper search has two additional incoming-bit
requirements that must be enforced before its scores describe valid machines.

This was a read-only audit of the candidate's raw native table, the seven
composed fixed tables, and the source dictionary. It involved no further search.
`macro_audit.json` contains the exact SHA256 of every input, all asserted source
bindings, and eight literal dispatch traces. The standard-library-only checker
can be run from any working directory:

```sh
python research/gate_search/check_macro_audit.py
```

It verifies **41 literal pair identities across eight tables**, twenty source
bindings, seven transparent entries, and eight three-transition traces. It reads
the package and prints its result without modifying files.

## Correct pair identities

Here `0Rj / 1Rk` means that the reader preserves the scanned bit, moves right,
and enters `j` or `k`. These are exact equalities of literal transition rows.

| Source construction | Children | Existing reader | Literal rows |
|---|---|---:|---|
| `node55 = (node49,node54)`, copy A | `(19,114)` | 98 | `0R19 / 1R114` |
| `node58 = (node49,node57)`, copy D | `(19,20)` | 12 | `0R19 / 1R20` |
| `node70 = (node49,node69)`, copy H | `(19,179)` | 166 | `0R19 / 1R179` |
| `node60`, two increments | `(61,61)` | 99 | `0R61 / 1R61` |
| `node61`, four increments | `(99,99)` | 190 | `0R99 / 1R99` |
| ORH shared reader | `(98,90)` | 333 | `0R98 / 1R90` |

The ORH rule applies only where state 333 is present. It is not a free macro
available in every fixed table.

The copy-H error was first diagnosed during symbolic runtime checking of
apparent 193-state nominees in the reduction search. This audit independently
confirmed the correction from two primary artifacts: the source dictionary
defines `node70` as `(node49,node69)`, and literal state 166 has read-one row
`1R179`. Consequently both `node69 -> 30` and `(19,30) -> 166` were wrong.
The corrected scorer is `corrected/screen_corrected.cpp`; the historical edit
is retained in `audit/scorer_correction.patch`.

## Copy remainders and transparent gate entries

The expanded copy remainders are:

| Source node | Native entry | Rows |
|---|---:|---|
| `node54` | 114 | `0R130 / 1R107` |
| `node57` | 20 | `0R30 / 1R31` |
| `node69` | 179 | `0R194 / 1R128` |

Each is a transparent reader. Its first transition establishes the preceding
bit needed by its child, so it introduces no additional immediate-entry
history-bit restriction. The same entry observation applies to `node6 -> 77`,
`node10 -> 109`, `node146 -> 196`, and `node149 -> 217`.

This observation does not replace the other construction obligations. Moving a
subtree can change resolved branch instructions or violate address bounds;
source equality, complete runtime contracts, and startup must still be checked.

## Entries that depend on the preceding bit

The relevant bit is the tape cell immediately to the left of the head when the
macro is entered. For a fresh transparent AX reader, it is the branch bit just
consumed: zero for a left child and one for a right child.

| Logical macro | Native entry | Required preceding bit | Wrong-history behavior |
|---|---:|---:|---|
| `node145` | 122 | **1** | After 0, implements `node4`: decrements register 5 instead of register 1 |
| `node147` | 130 | **1** | After 0, implements `node51`: selects `node50` instead of `node18` |
| `node142` | 194 | **1** | After 0, implements `node68`: selects `node50` instead of `node40` |
| `node72` | 69 | **0** | After 1, the read-zero branch reaches a different subtree entry |

The first two requirements are additional restrictions on the deep exposed-gate
search. The latter two were already represented in the ordinary scorer's
placement penalties.

For state 122 on scanned zero, the exact three-transition route is:

- Preceding 0: `122 -> 137 -> 30 -> 45`.
- Preceding 1: `122 -> 137 -> 70 -> 41`.

The source dictionary distinguishes `node4 = (dec 5,continueTo 1)` from
`node145 = (dec 1,continueTo 1)`. The different physical selector reached after
three transitions is therefore material.

For state 130 on scanned one, the routes are:

- Preceding 0: `130 -> 20 -> 30 -> 46`.
- Preceding 1: `130 -> 20 -> 31 -> 47`.

The source dictionary distinguishes `node51 = (dec 4,node50)` from
`node147 = (dec 4,node18)`. `node50` begins with increment 1; `node18` begins
with increment 5. In all eight recorded dispatch traces, both examined tape
cells are restored and the head finishes one cell to the right. No exterior
cell is read, so these are exact local facts for every exterior tape.

## Consequences for interpreting search results

The incoming-history restrictions on native 122 and 130 cannot be dropped when
those controls become exposed leaves. Unrestricted tree rotations may move them
to a left child and change the program. The historical unrestricted deep-gate
screen therefore cannot support a claim about all valid physical machines at
its reported score.

The ordinary corrected H/GDH search uses the corrected copy remainders and
already-protected gate entries. Its actual reachable fixed-state count is a
separate accounting issue addressed by the corrected scorer's reachability
pass. This macro audit establishes literal identities and finite dispatch
facts; it does not complete the arithmetic calibration or the Lean proof.
