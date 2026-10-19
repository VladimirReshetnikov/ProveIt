# Why zero and downward-closed targets fail

All references are pinned to ProveIt commit
`79957d7b290ec807d434959a0c6ecc06ee90b419`.

## Code zero is explicitly true

`Code254.lean` defines `C254.truth : C254 0`. Its decoder sends zero to
`T0 = imp (rel 0 0) (rel 0 0)`, that is, `(v0 ∈ v0) → (v0 ∈ v0)`.
The named theorems are `dec_zero` and `sat_T0`. Numerically, zero is also the
fixed point `wim 0 0 = 0`; the decoder handles this fixed point explicitly.
It is not a missing or ill-formed formula.

Source: [Code254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/79957d7b290ec807d434959a0c6ecc06ee90b419/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Code254.lean),
particularly `C254`, `T0`, `decF`, `dec_zero`, and `sat_T0`.

Therefore a target predicate accepting zero cannot satisfy
`C254(h) ∧ A(h) ⇒ C254(F)` without already proving inconsistency.
Every nonempty downward-closed subset of the natural numbers contains zero.
Hence no nonempty downward-closed numerical target, including `H ≤ 1`,
can be justified by this acceptance-transfer lemma.

## Zero really occurs at the acceptance site

This is not merely an invariant value that might be unreachable. In the
command-level enumerator, candidate 3 is
`P(2, P(0, 0)) = pack (nip 0) 0`. The initial candidates 0, 1, and 2 are,
respectively, `mp 0`, `drop 0`, and `mp 1`, and all leave cache `H=0`.
Thus candidate 3 reaches NIP with cache zero in a fixed finite execution.

Source: [Enum254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/79957d7b290ec807d434959a0c6ecc06ee90b419/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/Enum254.lean),
particularly `s0`, `pack`, `fetch`, `execAt`, and `cstep`.

For the precise 246-state register seed there is an even shorter explanation.
`LogicalSeed246.seed` is `(N,T,W,A,D,H,X,Y,L)=(3,0,0,0,3,0,0,0,0)`.
It equals `L2.toAS s` for the enumerator state
`s=(pl,np,tw,ws,d,h)=(0,3,0,0,3,0)`. Here `fetch s=(3,4)`,
`unP 3=(2,0)`, and `unP 0=(0,0)`. The two source reads set the command field
`A=2` and leave `D=3+0=3`; they preserve `H=0`. The dispatch consumes `A=2`
and enters the NIP node 152, so the first candidate after this seed reaches
NIP with zero cache. The nonzero seed field D therefore introduces no ambiguity.

Sources:

- [LogicalSeed246.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/79957d7b290ec807d434959a0c6ecc06ee90b419/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/LogicalSeed246.lean): `seed` and `primary_values`.
- [L2Root254.lean](https://github.com/VladimirReshetnikov/ProveIt/blob/79957d7b290ec807d434959a0c6ecc06ee90b419/Computability/BusyBeaver/Lean/BusyBeaver/ZFC/L2Root254.lean): `toAS`, `fetch_run`, `reads_run`, and `dispatch_nip`.
- [Dag254.v](https://github.com/VladimirReshetnikov/ProveIt/blob/79957d7b290ec807d434959a0c6ecc06ee90b419/lib/jeff-busy-beaver-zfc254/ZF/m254/coq/prog/Dag254.v): node 152 is `nip().0`.

The accompanying `seed_zero_control.py` independently evaluates the literal
219-node DAG from that seed. It reaches node 152 after exactly 64 nonterminal
RegisterPath leaves with the full vector `(4,0,0,0,3,0,0,0,0)` and entry prefix
`1110100101`. It records all 64 steps in `seed-zero-control.json`. This is a
finite source-level control, not a new kernel certificate or a statement that
64 binary steps suffice. The binary boot-to-seed claim remains the separate
246 baseline proof.

Replacing only the NIP test by `H==0` or `H<=1` therefore causes an unconditional
finite source halt from the 246 seed. Such a change cannot have nonhalting
calibrated to Con(ZFC), assuming ZFC is consistent.
