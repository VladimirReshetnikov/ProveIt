# Helical plane to literal marked word: author receipt

Date: 2026-10-26. Author: `complemented47_review`.

This receipt covers the new `WangTiles942HelicalQuotient.lean` and its
focused checks. It is an author self-review, not an independent peer review.
The author also wrote the imported literal-table permutation proof. No
existing source, shared documentation, or git state was changed.

## Frozen sources

Paths below are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942HelicalQuotient.lean` | 147 | 6496 | `dd7e2a20254aba54f57d03cc6690a6c18d3d45d83fe3c44383f53be4c3162481` |
| `WangTiles942HelicalQuotientChecks.lean` | 91 | 3924 | `5be0501091408ae5bee59a2b863e81edc93ed3552d209d02701a2434348b8034` |

The main module directly imports only `WangTiles942Periodic`
(`b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53`)
and `WangTiles942Permutation`
(`3351336105f22baf653dcefb3bd83273924dd539353eebf5f1232da855045cef`).
The checks import only the new main module.

## Verified statement and argument

For an actual tile plane `T`, assume that every tile is `Allowed`, its
horizontal and temporal colors match in the actual coordinate directions,
`T 0 0 = start`, and it has periods `(w,-1)` and `(0,H)`, with positive
natural `w,H`. `exists_marked_word` constructs a function
`a : ZMod (w*H) → Fin 942`, proves `MarkedWord (w*H) (w:ℤ) a`, and retains
the full equality

```text
tile (a (address (w*H) w x t)) = T x t
```

for every integer `x,t`. No coprimality, unique-Start, computation-run,
or pre-existing quotient factorization premise occurs.

The proof first establishes `T x t = T (x+w*t) 0` by integer induction
in both directions. Vertical periodicity then supplies the row-zero
period `w*H`. The function `z ↦ T (-z) 0` is periodic with that same
period, so it agrees with its `ZMod` canonical-representative values.
Actual allowed-table indices are selected using `allowed_iff_tile`.
The full signed-address identity follows before any matching argument.
Literal table injectivity recovers the exact Start index zero, and
the existing `address_east` and `address_next_row` identities transfer
both color matchings without changing their orientation.

This module proves the geometric quotient step. It does not construct
the periodic plane from a halting computation, prove cofinal widths or
heights, build a polynomial witness, or establish the complete
equivalence with `Con(ZFC)`.

## Builds, focused checks, and audit

The complete main and check sources were read before execution, and
the final full sources were read again before this receipt. Builds were
serial and capped, with `Elab.async false` in both sources:

```sh
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942HelicalQuotient.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalQuotient.lean
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942HelicalQuotientChecks.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942HelicalQuotientChecks.lean
```

Both final builds exited zero. The main log is empty. The first main
attempt needed two elaboration simplifications: reducing the integer
cast in the generic remainder identity, and unfolding the literal
`start` record when comparing index zero. Neither changed a premise or
mathematical claim. The focused checks passed on their first build.

Checks cover arbitrary signed time, negative integer representatives,
the temporal address sign (including the opposite-sign negative
control), noncoprime dimensions `w=H=2`, modulus one, the entire plane
binding, and the positive-dimension existential wrapper. The constant
plain-plane edge cases are deliberately used only for quotient binding;
they are not claimed to satisfy the Start premise.

All eleven `#print axioms` reports contain only subsets of `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, `native_decide`,
new axiom, or incoming program execution is used.

| Build log | SHA-256 |
| --- | --- |
| `/tmp/wang-tiles942-helical-quotient-main-stage1.log` (initial elaboration failures) | `d67b3a1cc47d2c29efe8f2e10d69024160b7ed369e7b3fe60eea66bc0dcd0dce` |
| `/tmp/wang-tiles942-helical-quotient-main-stage2.log` (final success) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/wang-tiles942-helical-quotient-checks-stage1.log` (final success and axiom reports) | `6c8b2ce883573a06bef5ea9e047895573cad8fc637aa39c241704cacc2f86851` |
