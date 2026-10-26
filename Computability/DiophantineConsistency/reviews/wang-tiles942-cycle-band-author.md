# Actual halted trace to finite marked word: author receipt

Date: 2026-10-26. Author: `complemented47_review`.

This is an author self-review, not an independent peer review. Only
the new main/check modules and this receipt were authored; no frozen
source, shared document, or git state was changed. The author also
wrote the helical extension/quotient and several machine-operation
dependencies. The trace-cycle and boundary modules were authored
separately by `circuit_reduction` and were fully read here; no build
of the new packet began before both dependencies were frozen.

## Frozen files and imports

Lean paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| File | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942CycleBand.lean` | 167 | 7485 | `feff6383911a22e0f496f95eff693d0ee757861831890f555cf85c5370de18e8` |
| `WangTiles942CycleBandChecks.lean` | 82 | 3382 | `adbc833379205c7784de10393dbe682654812d8962f7523aa26ef6ab639b1091` |

The main directly imports:

- `WangTiles942CycleBoundary`, SHA `a2f992dbfd4c14d70b8daf423c0b598d714131c5605cf29c833bc7dc2b808f8f`;
- `WangTiles942HelicalExtension`, SHA `1ca88d926e0002f2ee0eb7974176ebbe0f400c473e3b7ab742a44421b834bdc6`.

The frozen trace-cycle source is
`58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e`.
The checks directly import only the new main module.

## Constructed object and endpoint

The finite time index is the canonical value of `(t : ZMod H)`, so
negative times and reset-to-initializer wrap are included. At every
interior location, `band L H x t` is the actual `cycleTile` at that
time index. At `x=-L`, it is the literal allowed seam

```text
(previous edgeCode squared, 437, current edgeCode, 437).
```

Here the code is 2 in the initializer row, 1 in the reset row, and
0 otherwise. The previous code is evaluated at `t-1`. This gives
seam colors `(1,437,2,437)` at initialization and `(4,437,0,437)`
immediately afterward. It is exactly the `Allowed.seam` constructor
with two `Fin 3` arguments.

The boundary module proves the first interior west color equals
the current code and the last interior east color equals its square.
Those proofs derive zero run-row boundary signals from the actual
halted-trace bounds at both `t` and `t+1`, including stationary halt.
The final theorem therefore has no boundary-cleanliness premise.

`marked_word_of_halt T L R H` assumes only

```text
(DecimalMachine215.machine.run T).state = none
T+2 ≤ L, T+2 ≤ R, T+2 ≤ H, 3 ≤ H.
```

It constructs an actual `a : ZMod ((L+R)*H) → Fin 942`, proves
`MarkedWord ((L+R)*H) (L+R:ℤ) a`, and retains the exact identity

```text
tile (a (address ((L+R)*H) (L+R) x t)) = band L H x t
```

for all `-L ≤ x < R` and every integer time. Both margins and the
height remain independently enlargable. The proof first establishes
band allowedness, actual horizontal and temporal matching, its
twisted seam, vertical period, and Start at the origin. It then
composes the frozen helical extension and quotient theorems.

This is an actual-machine halt-to-marked-word theorem. It does not
assert that the machine halts, establish unique Start, complete the
number-theoretic controller, construct a polynomial witness, or
claim the complete equation equivalence with `Con(ZFC)`.

## Fresh builds and focused checks

Both complete sources were read before execution. The final main
source was read again before freezing. Both sources set
`Elab.async false` and `maxRecDepth 10000`; the main has a fixed
heartbeat budget. Builds were sequential and capped:

```sh
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942CycleBand.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942CycleBand.lean
lake env lean -M 6000 -j 1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942CycleBandChecks.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942CycleBandChecks.lean
```

Final main/check builds exited zero; the main log is empty. The first
main attempt needed only simplification of the seam's `if True`
branch and an unused-variable binder name change. No premise or
mathematical argument changed. Focused checks passed first attempt.

Checks cover negative time, modulus one for the generic time index,
the exact seam chronology, a negative control for replacing the
previous code by the current code, the literal initializer/Start
tiles, twisted boundary equality, the full endpoint, and arbitrary
independent left/right/height padding. All fifteen axiom reports
contain only subsets of `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, `admit`, `native_decide`, new axiom, or
incoming program execution is used.

| Log | SHA-256 |
| --- | --- |
| `/tmp/wang-tiles942-cycle-band-main-stage1.log` (initial elaboration) | `3adf481fac1ccafd3ed3253f13ba3ebf33792e7d2e4a006c657247bda4a45152` |
| `/tmp/wang-tiles942-cycle-band-main-stage2.log` (final success) | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/wang-tiles942-cycle-band-checks-stage1.log` (final success) | `b874c0c598cd8160b14da234a2b6c7c84b80b1eadf2b60946f4468fd9b3e240d` |
