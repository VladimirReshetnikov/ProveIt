# Exposed-marker presentation: the same 217-state machine

The submission in commit `673c87a878` is **the same machine up to state
renaming** as the [accepted primary 217](../../README.md). Its source is
byte-for-byte identical, and it uses the same 69/400 state merge. The two
savings cannot be combined to obtain 216 states.

| Native state here | Native state in the primary |
|---:|---:|
| 188 | 213 |
| 213 | 210 |
| 210 | 188 |
| All others | Unchanged |

[The complete comparison](comparison.json) checks all 434 transitions,
both canonical relabelings and all 4,750 internal source-prefix roles.
Thus each computation is identical step by step after renaming states,
on arbitrary tapes and from the blank tape. These exact native/prefold/source
bytes also match candidate025 from the primary's already published
[independent reconstruction](../../research/independent-helper-reconstruction/README.md).

The new report changes six retained rows relative to the dominated K218
parent, while the primary report changes nine. The difference is in how
states are named relative to that parent; the final graph and source are
isomorphic. The helper is called 188 here and 213 in the primary.

- [Native table](k217.native.tm): initial state 0 and halt 254.
- [Breadth-first canonical table](k217.tm): working states 0–216 and halt 217.
- [Canonicalization map](canonicalization.json).
- [Identical source](../../sites217.json).

The complete initializer is included. The alphabet is binary, the single tape
is two-way infinite and initially all zero, and every move is L or R. The
ordinary proof of nonhalting iff Con(ZFC), formalizable in ZFC, transfers from
the primary by the exact state bijection. The primary's fresh 6,176-case
runtime and complete 312,617-step startup remain the accepted evidence;
no redundant full runtime was rerun for this presentation. Three fresh
checks reproduce the submitted construction, four-case local proof, and
separate fixed-core source experiment.

The report's additional fixed-label calculus uses general gated membership
vacuity plus `N(nks(1,3,c))` for `c≥4`. It has an ordinary equiconsistency
argument, but its direct source costs 211 distinct subtrees versus the
primary's 203. It needs a revised whole AX compiler and binary implementation;
it is not a second 217-state construction or part of this machine's proof.

[Full intake comparison and proof scopes](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-194.md)
and [recovery/reproduction](../../../../../../../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-194-reproduction.md)
retain the manuscript, appendix, fresh checks and delivered evidence.
[The original notice](NOTICE.md) preserves attribution; its original-layout
references resolve in the recovered packet. The primary's notices and license
files retain the inherited construction's provenance. No new exact-table
Lean/PA theorem or minimality claim is made.
