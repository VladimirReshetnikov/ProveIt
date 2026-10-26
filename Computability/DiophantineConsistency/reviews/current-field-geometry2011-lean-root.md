# Exact cell geometry and the remaining whole-field exclusions

Date: 2026-10-26. Authors: controller_certificate (translation/coarse split)
and complemented47_review (generic cycles). Independent complete source
and check review and fresh replay of all six files: ROOT.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| CurrentCellTranslation2011.lean | c3e9811e9b5c60c8ed740b58277ed40569108f888347ffcbb84169ba31b5685d |
| CurrentCellTranslation2011Checks.lean | cdf55b1ea004d415075483ff00d1f9a500255c39f545192ca0ad26d3eebe0f03 |
| CurrentFieldOffsets2011.lean | b44a1eb24d23bf9e744fee99531cab653c34029e41a3ab14386f95d72b60c683 |
| CurrentFieldOffsets2011Checks.lean | 0146ee0c0e854876db4c808e88cd7d79052083c881238e288423ab0eee82c678 |
| NativeFieldCycles2011.lean | 9cac50de2b83d3b802eab615ab4340027b842abc910586d009c4847b913f8442 |
| NativeFieldCycles2011Checks.lean | 3682208abe906dade29dd135861743ec0e955e1a324a1841611cb1bf59e077ac |

ROOT read all151+59,143+57 and111+64 lines before executing the respective
files. All six direct fresh `lake env lean -M6000 -j1` runs exited0.
The three main logs were empty; all fifteen axiom reports are standard
only. Authors also freshly checked the frozen packets. These are module
replays against checked prerequisites, not an entire ancestor/umbrella
rebuild. Detailed author records: [translation](current-cell-translation2011-lean-author.md),
[coarse offsets](current-field-offsets2011-lean-author.md),
[generic cycles](native-field-cycles2011-author.md).

The cell type is the aligned subtype of the full ZMod(N*2011). For any
natural temporal field shift t, an explicit equivalence subtracts
t−t%2011, with inverse addition. Exact source identities and both residue
cases retain group subtraction and prove every natural cast subtraction
is bounded. Arbitrarily large shifts, adding full cyclic periods and
the single-cell case are covered; no field-level truncation is used.

Sparse support, all-cell selector count<=1 and only the three source ones
at1004−t,961−t,962−t give t%2011 in{0,19,20}. The marker excludes1..18
and bounds the remainder by1004. The961 source bounds it by961. Every
remaining offset21..961 puts two distinct actual selectors in the same
translated cell, contradicting its count. No Boolean, decoded-label,
occupation or current-marker-value premise is needed for this coarse split.

The offset19 generic lemma excludes South510 on any finite permutation
with the specified doubling recurrence and one fixed exceptional source
value. Three predecessors force that value to be511; parity on a positive
return period then contradicts510. The genuine511 self-loop is explicitly
witnessed in checks and is not excluded. The offset20 obstruction follows
from two local residue equations with error<=2 on an arbitrary type and
arbitrary source function; it needs neither finiteness nor bounded S.

These packets expose their source/copy/recurrence inputs. Actual mask
parity, decoded Start and terminal South values and nine-bit aggregation
must still supply those inputs before whole-field alignment follows for
polynomial zeros. The [implementation plan](current-whole-field-alignment-plan.md)
records that dependency order and the prohibited circular occupation and
marker assumptions. No complete native or consistency equivalence is
claimed by these separate geometry lemmas.
