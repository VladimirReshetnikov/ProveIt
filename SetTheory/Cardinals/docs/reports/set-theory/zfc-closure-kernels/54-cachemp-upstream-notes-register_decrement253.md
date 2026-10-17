# Positive decrement and the appended spare

`RegisterDecrement253.positive_decrement` proves the fourth general
register-box excursion for the actual compact253 machine. Together with
the earlier marking, increment and zero-decrement proofs, all four box
contracts now have whole-tape Core execution theorems. Dispatcher and
program-counter preservation remain separate work.

The attributed source contracts are `shift_dec_block`, `shift_dec`,
`Wf_rev` and `box_decp` in mira-emmy's public PR20, pinned head
`0d544f2a2e3c18f12278441a74b7879f31cbe856`,
`ZF/m253/coq/tm/Box.v`. Mira-Cult designed the original machine, Jeff
supplied its verification, and Andrew James Wade supplied the compiler
framework. This is a new Lean proof using actual `Table253` rows and
the existing `BusyBeaver.Core.runFrom`, rather than an imported Coq proof.

Write `bits(v) = 0 1^(v+1)`. The positive target has value `v+1`, so its
erased-first-one representation is `0 0 1^(v+1)`. Starting in compact79
(old seek.dec43), head `h`, the theorem transforms

```text
bits(pre)  0 0 1^(v+1)  bits(rest)  0
    into
bits(pre)  0 1^(v+1)    bits(rest)  0 1  0
```

The selected value becomes `v`. Following register values and existing
spares stay unchanged while their physical blocks move left one cell.
A complete new zero-valued block `0 1` is appended, followed by the blank
exterior. Omitting that block would violate the actual source invariant.
The resulting file is `(pre ++ v :: rest) ++ [0]`, one cell longer than
the old unmarked file `pre ++ (v+1) :: rest`.

The time is exactly `2*F+3`, where `F` is the old unmarked whole-file width.
The exit is compact8 (old63) if `pre` is empty, or compact10 (old48)
otherwise; the absolute head is `h-1`. All values and lengths in `pre`
and `rest`, all finite left contexts, and all integer heads are arbitrary.
The suffix may include nonzero spare blocks. There is no bound on prefix
length in this physical box contract. The right exterior is zero, rather
than an arbitrary unrelated data tail.

The proof explicitly detects a positive value, scans the suffix, shifts
its blocks left by an induction over the nearest-first left list, restores
the selected block, appends the spare and returns across the prefix.
If `B` is the suffix width, the part after the prefix seek costs
`3 + v + B + 2 + B + (v+2) + 2 = 2*(v+B)+9` steps.
Adding the outward and return prefix scans gives `2*F+3`.

The symbolic zipper theorem uses two final false cells. The public Core
theorem accepts the same one-padding input format as the earlier boxes.
`zipRep_pad_right` proves that appending one exterior false changes no
represented tape cell; it does not assume extra data is absent without
the whole input `ZipRep`. The output again includes one explicit false.
Thus the padding conversion retains both half-lines, the absolute head
and the arbitrary finite left context.

The nine new literal transition facts are checked directly by kernel
computation. Source compilation passes with the explicit Lean4.32.0
executable, followed by 24 axiom reports and five caller examples. The
literal facts and the list-fold composition lemma use no axioms; remaining
proofs use only standard `propext` and `Quot.sound`. There are no admissions,
custom axioms or native computation. Seven source-verified dependencies
are reused; the full bootstrap is not rerun. Exact commands, source hashes,
headers, timings and independent reviews are recorded in
`results/register-decrement253-verification.json`.

The theorem is for the positive-decrement box, including its actual return
state. It does not claim first arrival, a full logical `EDecnz` step, a
reachable program path, a dispatcher invariant, proof enumeration or a
consistency endpoint. The next layer must verify the finite site executor
and its use of these four general boxes, then connect its path updates
to `RegisterPath` on reachable configurations.
