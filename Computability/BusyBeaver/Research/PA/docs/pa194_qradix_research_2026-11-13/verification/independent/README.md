# Independent audit of the PA194Q5 and PA194Q6 constructions

This directory contains a second source parser and a literal-tape verifier for
the two constructions. Neither executable imports the construction compiler.
Run with Python 3.10 or later and enabled assertions:

```sh
python3 -B source_audit.py ../../machines/PA194Q5 ../../machines/PA194Q6
python3 -B check.py ../../machines/PA194Q5 ../../machines/PA194Q6
```

Paths above assume this directory is the working directory. The machine
directory arguments may be moved or renamed. Each must contain `machine.tm`,
`native.tm` (or `machine.native.tm`), `labels.json`, `sites.json`,
`instructions.json`, `nodes.json`, and the construction `receipt.json`.
The optional `--output PATH` selects where to write the audit receipts.
The scripts use only Python's standard library and the files under `reference/`
and `inputs/` supplied here.

## What the source audit establishes

`source_audit.py` parses the pinned upstream `Program.lean` itself. It expands
the exchanged quantifier-distribution grammar with coefficient 5 or 6 and
checks every reported primitive source site against that independent expansion.
Two separately implemented source-control-flow resolvers agree. The audit also
compares the source with its primary-grammar M5 or M6 parent: every primitive
site and resolved transition outside the axiom emitter remains identical.

A symbolic stack evaluator works over a free constructor algebra, preserving
the coefficient as an explicit parameter. The old and new emitters each push
exactly ten items. Their only differing pushed item is the sixth principal
head, at index 8 in the whole push sequence:

```
old: U(D,A) -> (U(D,I(A,H)) -> U(D,H))
new: U(D,I(A,H)) -> (U(D,A) -> U(D,H))
```

The unguarded top value, guard macro suffix, and all other pushed items agree.
The original MP and Shift source subtrees are checked explicitly. This avoids
confusing these constructions with the existing PA194Q controller, whose
cached-value behavior differs.

The evaluator uses the stated mathematical contracts of the inherited
arithmetic macros. It independently checks their composition in the exact
emitter; it does not claim to have newly formalized those macro contracts.

## What the literal-tape audit establishes

`check.py` validates all 388 rows, the 194 nonhalting states, the unique
halting target, the dense/native label bijection, and graph reachability of
every counted state. It reconstructs the four arbitrary finite-list sweep
lemmas from the candidate's own literal transition rows. The inherited engine
then checks every primitive site, including both zero and positive branches of
every decrement.

The contracts quantify over nine independent natural register values, an
arbitrary nonempty finite spare list, an arbitrary nonnegative header gap, and
the entire tape with blank exteriors. Unary self-loops are iterated using exact
affine run lengths; finite-list sweeps are justified by the reconstructed
one-block derivations and induction on the list. No arithmetic-box oracle or
sampled register corpus substitutes for these contracts. Each contract records
a positive affine duration, its net head motion, and the literal rows used.

Blank startup is separately executed with the complete finite support of the
tape, and its exact result is compared with the required clean frame. This
finite startup calculation is not being used to infer nonhalting.

## Provenance and limits

The pinned repository snapshot is
`317b07268681b44ff352d173a162e2a8c241b2fe`.
`inputs/provenance.json` records the paths and SHA-256 digests of the upstream
program and both grammars. The `reference/` files are byte-for-byte copies of
the independent checker bundled in
`Computability/BusyBeaver/Research/PA/docs/pa194_radix_family_2026-11-13/verification/reference/`
at that snapshot. The retained `reference/README.md` documents their earlier
origin; the original licenses are included. The wrapper changes only the
header-base parameter and the register/control label translation needed to
identify the candidate's entry points.

These are executable mathematical audits, with explicit induction rules in a
small symbolic interpreter. They are not an end-to-end Lean or Rocq proof of
the new PA consistency equivalence. The logical bridge additionally uses the
mathematical primary-machine correctness theorem, the coefficient-coding
argument, and the propositional theorem exchanging two curried antecedents.
The latter is already a concrete derivation in the pinned upstream files:
`PA196/Logic/ImplicationBasis.lean`, definition `Dominated.exchange`, and
`PA196/Logic/Deduction.lean`, definition `r2`, which applies that derivation
to precisely the sixth head. These files are under
`Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196/` in the pinned
repository. The reverse exchange uses the same theorem with its two
antecedents interchanged.

The output receipts bind the claims to the exact source and transition-table
digests. Rerunning the scripts, rather than trusting the stored receipts, is
the intended verification route.
