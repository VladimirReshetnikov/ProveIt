# First arbitrary-length register excursion for public253

`RegisterBoxes253.zero_decrement` proves actual execution of the attributed
253-state machine's zero-decrement register box. Its preceding registers,
following registers and spare blocks, absolute head, and finite left context
are arbitrary. This advances the general runtime proof beyond the already
proved finite bootstrap and its register-frame correspondence.

The source contract is mira-emmy's public PR20, head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`,
`ZF/m253/coq/tm/Box.v`, particularly `fwd`, `ret_file` and `box_dec0`.
Mira-Cult designed the original machine, Jeff supplied its verification,
and Andrew James Wade supplied the compiler framework. The new Lean proof
uses the actual compact `Table253` transitions. It neither imports the Coq
proof nor treats the different 254-state table as an isomorphic machine.

For a register value `v`, write `bits(v) = 0 1^(v+1)`. Let `B` be the width
of all preceding registers, the sum of `v+2` over `pre`. Starting at head `h`
in compact state79 (old seek.dec43), the right tape is

```text
bits(pre)  0 0  bits(rest)  0
```

The two zeros mark a selected register of value zero by erasing its first
unary one. In exactly `2*B+5` steps the machine reaches compact state23
(old return3), head `h-1`, with the complete output register file

```text
bits(pre)  0 1  bits(rest)  0
```

The arbitrary left context is retained. `leftAt` accounts for the new head
cell even when that context is empty. The final explicit zero is exterior
padding, allowing an empty suffix; every cell beyond the lists is also
specified as zero. `rest` can contain an arbitrary spare suffix, including
nonzero values. There is no bound on the number or values of preceding
registers. The logical simulation will later restrict selection to the first
nine primary registers.

The proof composes a forward seek of `B` steps, four literal steps detecting
zero and restoring its one, and a return of `B+1` steps. Nine row equalities
are checked directly against the compact table: old43/0,43/1,59/0,59/1,
75/0,0/0,1/0,1/1,3/1. The old states 43,59,75,0,1,3 map respectively to
compact79,93,110,19,21,23.
The excursion stops before the outgoing old3/0 transition, which the public
253 reduction changed. Its use of old3/1 while returning across earlier
registers is separately checked against the actual253 row.

`ZipperRuns` supplies generic sequential zipper execution, its soundness for
the existing `BusyBeaver.Core.runFrom`, and arbitrary-length preserving left
and right scans. `RegisterBoxes253.registerBits_eq_flatMap` identifies its
unary file with the exact block expression used in `Boot253`. The final
`zero_decrement` theorem has a whole-tape `ZipRep` conclusion; separate state,
head and pointwise tape corollaries expose its effects. This does not assume
a register-box oracle or infer a general execution theorem from finite tests.

The source convention differs from `WadeMachine.SelectedRegister`: here the
erased selector has `value` ones after its two zeros. That frozen252 predicate
has `value+1` ones after its two zeros and cannot be substituted unchanged.

Both new modules compile with the explicit Lean4.32.0 executable. A separate
caller file checks 27 axiom reports and four interface examples, including
a blank-tape zero-box input and a separately quantified spare suffix. The
nine literal transition facts use no axioms; the execution facts depend only
on the standard `propext` and `Quot.sound`. There are no admissions, custom
axioms or native computation. Only the three source-verified dependencies
Core, Table253 and FiniteZipper are reused; the full bootstrap is not rebuilt.
Exact commands, hashes, headers, scope and timings are in
`results/register-boxes253-verification.json`.

Independent read-only reviews by the basis and theory reviewers found no
contract defect. The general scans, whole-tape semantics, compact state map,
time bound, empty-context cases and return endpoint were inspected.

This is a zero-decrement **box** theorem. Selection/marking, increment,
positive decrement, PC transformations, dispatcher preservation, reachable
program-path invariants, proof enumeration and the internal consistency
endpoint remain open. The result makes no first-arrival or complete logical
`EDecnz` claim. The next modular source contracts are `box_mark`, `box_inc`
and `box_decp`; positive decrement must preserve the arbitrary suffix while
appending the extra zero block required by the original source invariant.
