# 250-state prefix-carry consistency machine

This directory freezes the same exact machine delivered in commits
[`126d12e470`](https://github.com/VladimirReshetnikov/ProveIt/commit/126d12e470c2d3773b9c128720a8ba202b760087)
and [`6993a40aef`](https://github.com/VladimirReshetnikov/ProveIt/commit/6993a40aef24be8f61edaa27686cca12781cd583).
Independent review found no fatal defect in its ordinary mathematical proof
within the reviewed scope, and all requested executable audits reproduce.
The exact-table Lean endpoint and the equivalence proved inside PA are work
in progress. The existing 252-state Lean endpoint does not certify this table.

| Artifact | States and entry | Identity |
| --- | --- | --- |
| [Canonical table](zfc_prefix250.tm) | 250 working states 0–249, start 0, dispatch 92, halt 250 | SHA256 `0626819c4842f224001e7685366d8061897a7bc9470c015129a1d1cf22efb36e` |
| [Original labels](zfc_prefix250_old.tm) | Start 97, dispatch 96, halt 254 | SHA256 `fd455304bad82a6da7ab83149352d0b1db27557582c4cc6312de003c96ff4e43` |
| [Renumbering](renumbering.json) | Exact bijection, including separate halt | Both forms have 500 transition rows |

The machine uses a binary, two-way infinite, single tape, entirely zero at
startup, with head 0. Every transition writes a bit and moves left or right,
including the transition into halt. Initialization is included in the 250
working states. The intended theorem is blank-tape nonhalting iff Con(ZFC).
The reports give an ordinary proof of the equivalence in ZFC; the project's
stronger PA formalization remains unfinished.

The [literal table and finite graph facts](../table_prefix250.md) are now checked
in Lean: 40 theorem audits and 40 callers pass, with only standard `propext`
where axioms occur. Lean now also checks the [unbounded register operations](../prefix250_boxes.md),
[selectors](../prefix250_mark.md), [symbolic execution](../prefix250_symbolic.md),
[frame adapters](../prefix250_frame.md), and [first 1,024 blank steps](../boot_prefix250_first.md).
Complete coverage, runtime composition and the final startup remain in progress.

The reduction preserves the complete original proof-search program. It shares
a carry/rollback circuit between register operations and reuses a runtime
state for initialization. Increment adds a spare block; positive decrement
shifts the register-file boundary by one cell. A nonempty spare suffix and
the head-to-header distance invariant support arbitrarily long computations.

The fresh nine-check audit verifies all 8,391 guarded cases and the complete
585,431-transition blank startup, reaching logical registers
`(N,T,W,A,D,H,X,Y,L)=(1,0,0,0,4,0,0,0,2)`, with 210 spare blocks and 438 one-cells.
It also checks the universal induction templates, full-PC correspondence,
marking footprint and retiming identities. The separate literal regressions
are finite controls; nonhalting is not inferred from a long execution.

The [intake reconciliation](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-160.md)
contains the mathematical findings and exact proof boundaries.
The [reproduction instructions](../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-160-reproduction.md)
recover the full reports and executable packages from Git and list fresh results.
No unavailable original-author file is needed for these audits.

Mira-Cult designed the original calculus and 254-state machine; Jeff Ketchersid
provided its verification; Andrew James Wade provided the compiler framework.
The public 253 reduction is credited to mira-emmy. ProveIt's permutation252,
formal developments, and the earlier working prefix/pulse research retain
their respective attribution. The second 250 package strengthens the audit of
the same construction and does not claim discovery of its core idea or worldwide
priority. Preserved licenses do not replace the terms of upstream material.

No proof of Con(ZFC), unconditional nonhalting, state-count minimality or
249-state solution is asserted.
