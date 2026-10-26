# Actual clock1 row and derived absence of premature finishes

Date: 2026-10-26. Author and full source/check reviewer: ROOT. This is an
author receipt, not an independent peer review.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942RowEncoding.lean (76 lines) | d9c24628856b55b6e91b843208539982810d84fbb6f2b5882382b61f4a3cb9df |
| WangTiles942RowEncodingChecks.lean (41 lines) | bd4ffcc7b65d3200f610168ec69108ffc75df19e18d17113e85aab12da7ed6c5 |
| WangTiles942OperatingRow.lean (71 lines) | f92a15534d5bfdfedb124aef9dac8cc2660b4eacd78562be25066ce66c02e443 |
| WangTiles942OperatingRowChecks.lean (39 lines) | 6534650b8a59d225db8aa0fd64067fcf795560c33942e64dd33febaf3f4cae88 |

All four complete files were read before their fresh direct bounded Lean
executions with `-M6000 -j1`. RowEncoding passed its first main/check runs.
OperatingRow's first main reached the default elaboration recursion limit
at the Boolean output bound. The final source explicitly reduces that
goal to the actual action's Bool.toNat bound and uses maxRecDepth10000;
those changes were read before replay. Its final main and first checks
passed. Both final main logs are empty; all ten axiom reports use only
the standard axioms. Each checks file imported the main object freshly
generated from its final source. No full dependency or umbrella rebuild
is claimed.

RowEncodes means only an interior head and actual encoded north colors
at every integer point inside the open interval. It contains no transition,
no-finish, exterior-tape or run-correspondence field. The exact initialized
color function and actual vertical matching identify row1 with the actual
clock1 configuration. MarkedWord alone supplies both this row and the
derived PersistentStrip. The local projections recover the operating
head input, plain input colors, head uniqueness and the upper bound433.

OperatingRow uses the actual tape read as a Fin2 symbol. The exact input
grammar forces its operating head tile to the actual transition row at
index2*q+b, whose South output is Boolean. If any interior tile had
South438, the derived whole-row finish/reset theorem would force South438
at that same operating head. The contradiction excludes all interior
South438 edges and actual finish tiles. Absence of finishes is therefore
derived from actual matching and geometry, never assumed.

The checks preserve genuine locally Allowed finish tiles for plain inputs
and a halted head input. The operating-state premise is essential to this
exclusion. Further checks retain actual clock1, unique encoded head inside
the strip and the boundary-color435 obstruction even for a halted head.

The actual next-row step, eventual halting, reverse construction and
internal-ZFC proof remain further obligations. These packets do not claim
the final consistency equivalence. The decimal equation and metrics are
unchanged.
