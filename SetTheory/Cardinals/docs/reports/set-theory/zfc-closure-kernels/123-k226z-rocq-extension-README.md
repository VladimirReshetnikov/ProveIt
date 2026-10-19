# Closed Rocq endpoint for the literal 226-state machine

The primary target in this directory is the exact dense binary table whose
SHA-256 is

```text
b58279b8b2e2cf029dd94e084d47cd6097772d7bce2a62653767895123d29599
```

It has 226 working states, 452 transitions, blank input, initial state 0,
and terminal state 226. `coq/226/Dense226.v` gives it its own finite state
type; deleted states are not hidden in that state count.

The endpoint is `K226F.CorrectDense226`. Its two main theorems are:

```coq
tm226_halts_iff_ZFC_inconsistent :
  Dense.halts dense_tm Dense.c0 <-> StandardZFC ⊢TC ⊥.

tm226_nonhalting_iff_ZFC_consistent :
  (~ Dense.halts dense_tm Dense.c0) <-> ~(StandardZFC ⊢TC ⊥).
```

Here `StandardZFC` is the pinned reference's explicit first-order ZFC
theory, and `⊢TC` is its classical derivability relation. The endpoint
prints both dependency assumptions. A successful build requires two
`Closed under the global context` reports and no `Axioms:` report.

## Rebuild

Use Rocq 9.1.0 and rocq-stdlib 9.0.0. From the enclosing research package:

```sh
python3 vendor/k230-rocq/build.py --reference vendor/jeff-reference --coqchk
python3 rocq-extension/build.py
```

The first command freshly compiles all 216 pinned reference sources and
checks its original endpoint. The second verifies all extension source
hashes, checks the exact literal-table and source-tree bindings, freshly
compiles all 19 selected extension files, audits both final theorems,
and runs the matching `coqchk` on `K226F.CorrectDense226`. Both commands
produce logs and machine-readable receipts in their own `.build` folders.
No compiled proof objects are required in the archive.

For a nondefault layout, give both dependency paths explicitly:

```sh
python3 rocq-extension/build.py --reference /path/to/k230-rocq --jeff-reference /path/to/jeff-reference
```

`--coqc /path/to/coqc` selects the compiler. With an active opam switch,
the script also checks the installed stdlib package version. It always
checks a stdlib API probe.

The fast data check does not invoke Rocq:

```sh
python3 rocq-extension/build.py --check-only --all
```

To check deterministic generation of the selected proof sources:

```sh
python3 rocq-extension/regenerate.py
```

This reconstructs every selected `.v` file from the pinned reference,
literal inputs, and included proof templates, then compares all generated
hashes with the frozen `coq/226` sources. The generator is untrusted: the
subsequent Rocq build independently checks its emitted proof claims.

`--states 227` and `--states 229` select the two retained intermediate
endpoints. `--all` rebuilds all three. `--compile-only` omits the additional
`coqchk` run; its receipt says `PASS_CLOSED_COMPILE`, not
`PASS_CLOSED_KERNEL`.

## Proof structure

The proof keeps the original K230 source, calculus, and set-theory
calibration unchanged. The pinned repository is
`elliotglazer/k230-rocq` at
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`; its Jeff dependency is pinned at
`c132d7eae8158cd3a9850ea3eb7251158c3dd821`.

For the new literal runtime, eleven files are derived from the original
runtime files. Their changes are limited to the isolated namespace,
the actual transition array, disabled sparse labels, the exact bootstrap
step count, the new source tree, and its maximum path depth. The bootstrap,
four register-block lemmas, interpreter-site checks, and whole-program
simulation are replayed against the changed table. The new proof does not
assume a separate guard theorem about the new native state folds.

`OffsetBisim230.v` supplies the new source certificate checker. It permits
an integer offset in register 5 at paired checkpoints, while requiring
the tested register to have offset zero. The 226 certificate has 2,376
entries and 4,750 checked branches. Its eight nonzero offsets are all +1
at tests of register 6, corresponding to the four increment-and-drain loop
rotations. Both directions of this certificate are checked by computation
inside proved soundness theorems. The exported source equivalence holds
for every initial natural-valued register file.

`Dense226.v` then relates the sparse runtime labels to the exact dense
table. A total finite transition identity checks all 227 elements of the
state type, including the terminal state, and both tape symbols. The
resulting blank-input halting equivalence composes with the new source
equivalence and the unchanged K230 logic/calibration theorem.

The public input and proof bindings are checked separately:

- `inputs/226/table.tm` is compared with `Table226.v` and has exactly 452 rows.
- The sparse table is compared with `Table230.v`, with disabled slots
  retaining irrelevant data but having no executable transition.
- The dense/sparse relabelling is checked directly from both literal tables.
- `inputs/226/sites.json` deterministically reconstructs `Prog226.v`.
- The frozen offset certificate equals the certificate compiled by Rocq.
- `regenerate.py` reproduces all 19 selected extension files exactly.

The 226 source has 5,121 leaf occurrences, maximum path depth 41, and 188
distinct decision nodes. Including its 23 primitive leaves gives 211
distinct source subtrees. Decision-node counts and native TM state counts
are different quantities.

## Formal boundary

The final artifact is an external Rocq proof of the exact finite halting /
syntactic-inconsistency equivalence. The inherited set-theory development
uses finitary interpretations and proof translations; the new steps are
finite arithmetic source checks and literal Turing-machine simulation.
These arguments admit formalization within ZFC. This directory does not
claim to contain a serialized derivation written in ZFC's own proof syntax.

There are no new axioms, admitted proofs, native-computation shortcuts, or
assumed empirical test results in the endpoint. Finite native regression
and the separate symbolic runtime audit remain useful independent checks;
the Rocq endpoint does not import their receipts as hypotheses.

`receipts/` retains verification logs and exact hashes from the delivered
run. The default build always produces fresh receipts. Files under
`coq/` are the frozen proof sources; `.build/` contains disposable compiler
outputs. The original reference sources and their build are never edited
by this extension builder.
