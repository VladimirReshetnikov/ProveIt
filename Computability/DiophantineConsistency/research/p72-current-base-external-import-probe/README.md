# Narrow P72 current-base external import probe

This checks one combined import: the authenticated fresh current14 standard
endpoint together with `Mathlib.Algebra.MvPolynomial.CommRing`,
`Mathlib.Algebra.Order.Ring.Cone`, and `Mathlib.Data.Fintype.BigOperators`,
the three source-declared external names new to the 1,599-module P72 closure
relative to the current14 snapshot. The first two were also included in an
earlier successful normalized106 combined-import probe; this source adds the
Fintype module. It checks only `True` and does not build a P72 project module.

Actual outer session 29817 exited 0; both monitored dependency and Lean
compilation runs exited 0, and the output is `True : Prop`. The retained
[state](attempt01/state.json) SHA-256 is
`1e5cea4e85ccdc05af1c0407ba4fd598965be89b9ae63604929fd44aeaa831a5`;
the object SHA-256 is
`199e97968166803a7a03154c5b4f903554cee89b4301fefc4ba31d662f8bceb3`.
Source SHA-256 is
`084065e7503aca970b0874e12c83e78827ba03387143dbfb8e2ecdb129be5d83`;
runner SHA-256 is
`145e37570b6b031f10af05f2d8e3d0cd29b28d44fce94842832bfa20426eae0f`.
The prior 210-slot current14 preflight was rerun before and after; this run
also records 150 path/companion slots and requires direct dependency routing
and matching before/after observations. The Fintype object is pinned as a
point-in-time package input, not rebuilt or proven from source here.

Compilation ran 2.013 seconds, with peak sampled session RSS 2,831,155,200
bytes, minimum sampled host available memory 18,907,455,488 bytes, and no
stop, descendant or monitor error. The 5-GiB session RSS, 10-GiB host floor
and 180-second thresholds are sampled. This successful one-case probe does
not establish transitive provider compatibility for the 681 additional
P72 source modules or full dynamic ancestry.
