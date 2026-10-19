# Formalism reductions and independent source/machine proofs

This directory adds one concrete formalism reduction to the five incoming
238/237-state research archives, an independent proof of the team's new
236-state fold, and universal lemmas for further source transformations.

## Independent proof of the new 236-state fold

`../sections/fold236.tex` proves the fold `223 -> 182` on the team's
reassociated 237-state table. Old state 182 has one incoming row that writes
1 immediately to the left; old state 223 has one incoming row that writes 0
there. The merged state's new rows branch through that distinguishing bit.
Four three-step blocks reproduce the old steps exactly, and all remaining
470 rows agree under the state map. This gives halting equivalence on every
common initial tape and head position, including exact terminal tape and
head agreement. Each old step is simulated by one or three new steps.

```sh
python3 -B ../verification/check_fold236.py
```

Use `--old` and `--new` to select the packaged inherited-label tables when
the surrounding directory structure changes. The independent checker
imports neither the search code nor the generic fold checker. It checks the
two complete predecessor lists, all 470 ordinary rows, four exceptional
blocks, exact state sets, and the table byte hashes. Its receipt is
`generated/candidate236_handproof.json`. Python optimized mode is explicitly
rejected because the premises are checked with assertions.

The unbounded proof is given in the text. It is not a new proof-assistant
endpoint or an internal PA consistency theorem. Source equivalence and the
source-to-machine proof belong to the team's separately packaged artifacts.

## A complete 688-bit equational presentation

The best inspected equational baseline is the complete 713-bit packet in
`zfc238-composition-20261019/foundations/generated/E713.json`. Its second
equation, `d = N(d,N(d,d))`, follows from the other seven equations. Removing
it saves exactly 25 bits in the unchanged codec, producing a 688-bit packet
with the same signature, endpoints, models, and equational consequences.

## Proof

The retained closure equation has the form `d = F(d,r,...)`. Its Boolean
cofactor at `d=0` is exactly `r`; equivalently,

`(not d) and F(d,r,...) = (not d) and r`.

The retained NAND-class constructor produces the ground class
`k = P(d,P(d,d))`, whose incidence is Boolean truth at every stream,
regardless of the incidence of the class `d`. The native head equation
gives `V(P(k,d),d)=k`. In the ground closure instance with descriptor
`P(k,d)`, the matrix value `r` is therefore truth. The cofactor identity
then forces `d` to be Boolean truth. This is precisely the deleted axiom.

`e688_section.tex` gives the complete proof and exact limits. It uses the
published Boolean-algebra consequence of the Sh1 axiom, whose primary source
and proof files are at <https://www.cs.unm.edu/~veroff/BA/>. The inherited
E713/raw-EPSC/ZFC calibration is copied unmodified as
`reference/kernel_section.tex`, with pins in `reference/source_pins.json`.

## Reproduce

```sh
python3 -B build_e688.py
```

The script uses only the Python standard library. It independently re-encodes
the exact inherited E713 AST before making its one deletion, reconstructs the
literal closure equation, checks all 512 Boolean assignments to the cofactor
identity, round-trips E688, and rejects all 688 strict prefix truncations plus
three malformed controls. It imports no inherited packet generator.

Generated deliverables:

- `generated/E688.bits`: all 688 bit characters, plus a final newline.
- `generated/E688.json`: ordered signature, all seven AST equations, ground
  endpoints, and exact metrics.
- `generated/E688.equations`: every equation fully expanded.
- `generated/top_forcing_recipe.json`: the actual finite ground substitution
  used by the proof; this is not an expanded Sh1-only rewrite trace.
- `generated/verification.json`: exact checks and measurements.

E688's bit-character SHA-256, excluding the newline, is
`9518c474861557da085c76ef77dd4141eecfa0befaec66d90acc81ac39264d97`.

## Further deletion control

`tail_deletion_model.tex` gives an explicit infinite model of the six-equation
theory obtained by deleting E688's native tail equation. The ground endpoints
remain distinct. ZFC constructs this model directly, without assuming its own
consistency, so this second deletion would lose the desired calibration.

The model uses the finite/cofinite Boolean algebra on the natural numbers,
with top `d=0`; a selector that always returns the stream head; formula classes
whose values ignore the stream; and ordinary `<` as interpreted membership.
Constant-true descriptors use the unbounded-output branch, while constant-false
descriptors use the empty hull. The exact tail equation fails at `x=1,s=j=0`.

```sh
python3 -B check_tail_deletion_model.py
```

The resulting `generated/tail_deletion_checks.json` records 6,208 literal AST
checks and the explicit failing tail instance. The all-natural model proof
is in the accompanying text; it is not inferred from the finite checks.

## Independent fold-checker audit

This branch also reviewed root's separate reusable fold checker. Its audit
is `checker_audit/source_audit.md`. Two generic boundary failures were found
and repaired by root: deleting the halt symbol, and transforming an initial
input bit. Both have concrete old-one-step-halter/new-loop regressions:

```sh
python3 -B check_fold_checker_regressions.py \
  --checker ../verification/verify_state_fold.py
```

The repaired checker rejects both invalid maps. The audit also explains
inductive bit facts, exhaustive symbolic branching, whole-tape comparison,
positive blocks, and the permitted loss of terminal head/tape information
for a halting-only theorem. These tests concern the generic checker boundary;
the reported failures did not apply to the accepted `235 -> 98` reduction.

## General source lemmas

`source_rewrite_lemmas.tex` supplies universal proofs and explicit conditions
for equality of ordered control graphs, context substitution, reassociation
with adjusted break/continue levels, safe increment commutation, and moving
an increment through a terminating transfer loop. It also identifies two
real obstructions: an implicit decrement-zero jump cannot have its level
changed, and removing a right ancestor can make the old target of a
continue unrepresentable. These lemmas extend the search space without
inferring source equivalence from finite register tests.

## Inherited logical source and seed audit

`source_chain_audit.md` records the exact theorem chain from the rotation240
source to ZFC refutation, including the explicitly calibrated safe seed
`(3,0,0,0,3,0,0,0,0)`. The inherited static interface checker was replayed
against the files present in the new package; its passing receipt is
`generated/logical_source_interface_audit.json`. The audit distinguishes
the original rotation240 startup count from the new candidate's separate
finite startup proof.

## Status and attribution

The reduction and its independent codec/checker are new in this task. Sh1,
raw EPSC, the native stack, complemented binder, closure factoring and packet
codec retain the incoming archive's attributions. The exact inherited source
is preserved under `reference/` and is not relabeled as new.

The same-model argument is ordinary mathematics formalizable in ZFC.
It preserves the incoming E713 consistency calibration with its stated
dependencies. It is not a newly compiled Lean/Rocq theorem, a completed
internal PA proof-code comparison, or a Turing-machine state bound. A full
binary search machine must still charge the ground-rewrite checker and the
complete packet writer and startup.
