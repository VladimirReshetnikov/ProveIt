# General marking and increment excursions for public253

Two further whole-tape execution theorems now use the actual compact253 table:
`RegisterMark253.mark` and `RegisterIncrement253.increment`. They complement
the earlier zero-decrement box; they do not yet prove a complete register
instruction from one dispatcher visit to the next.

The attributed contracts are `skip`, `box_mark`, `shift_inc` and `box_inc` in
mira-emmy's public PR20, pinned head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`,
`ZF/m253/coq/tm/Box.v`. Mira-Cult designed the original machine, Jeff supplied
its verification, and Andrew James Wade supplied the compiler framework.
These are new Lean proofs from the actual compact table, rather than imports
of the Coq proof or assumptions about the original254 table.

Write `bits(v) = 0 1^(v+1)` and let `B` be the width of all blocks in `pre`.
For marking, the input state is the skip state for `pre.length`, where
`pre.length < 9`. The published old states
`[60,44,31,56,38,40,28,64,69]` map to actual compact states
`[17,15,13,11,9,7,5,2,122]`. Starting at head `h`, the excursion transforms

```text
bits(pre)  0 1^(v+1)  bits(rest)  0
    into
bits(pre)  0 0 1^v    bits(rest)  0
```

in exactly `2*B+3` steps. It erases the selected block's first unary one,
preserves all other cells, and ends at head `h-1`. The exit is compact20
(old2) for an empty prefix and compact24 (old6) otherwise. The input contains
the selected register explicitly; no unnecessary nine-block minimum is
assumed. Its value, preceding values and following/spare blocks are arbitrary.

For increment, the input is already marked and the entry is compact87
(old seek.inc73). Let `F` be the width of the **old unmarked whole file**
`pre ++ v :: rest`. The excursion transforms

```text
bits(pre)  0 0 1^v    bits(rest)  0
    into
bits(pre)  0 1^(v+2)  bits(rest)  0
```

in exactly `2*F+3` steps, ending at compact10 (old48), head `h-1`. It restores
the selector and adds one to the selected value. Every following register
value is unchanged, while its physical cells shift one position right.
The arbitrary left context and preceding blocks stay fixed. There is no
bound on prefix length or values in this physical increment contract; the
eventual logical selection adapter will restrict it to the primary nine.

Both results quantify over all integer head coordinates, arbitrary finite
left lists and every actual Core configuration satisfying the input
`ZipRep`. The right list has one explicit exterior zero; all cells beyond
the finite file are also zero. The right side is not an arbitrary unrelated
data tail. An arbitrary finite spare suffix is represented as further unary
blocks and is fully retained, including nonzero entries. Every input and
output cell is specified by the whole-tape relation.

The marking proof combines exact prefix skipping, three literal marking
transitions, and a return across the prefix. Its generic return scanner is
parameterized by a machine and three transition facts, so it also supports
increment's distinct return states. Increment combines a prefix seek,
two restoration steps, an inductive suffix shift, and a return over the new
file. The suffix-shift theorem covers an empty suffix and a zero selected
value. All execution transfers through `ZipperRuns.zipRun_sound` to the
existing `BusyBeaver.Core.runFrom`; no register-box oracle is assumed.

The two source modules pass explicit Lean4.32.0 kernel checks, followed by
a separate caller file with 35 axiom reports and four interface examples.
The 20 literal-fact declarations (including the finite skip families) cover
35 transition equalities and use no axioms. General execution uses only the
standard `propext` and `Quot.sound`. There are no admissions, custom axioms
or native computation. Existing source-verified zero-box/zipper dependencies
are reused; no bootstrap is rerun. Exact commands, source hashes, headers,
timings and independent read-only review are recorded in
`results/register-mark-increment253-verification.json`.

Positive decrement remains the fourth register-box obligation. PC updates,
site-checker soundness, reachable-path/no-stray-bit invariants, dispatcher
preservation, enumeration and the internal consistency endpoint remain
separate. These theorems do not assert first arrival at their return states,
and the marker-return endpoint is not the increment-entry state. A missing
dispatcher proof cannot be replaced by composing those two endpoints as if
they were adjacent transitions.
