# Actual marked window: independent peer review

Result: **PASS within the polynomial-to-marked-word scope.** I read all
148 main lines and 69 focused-check lines, the complete occupation and
periodic-word dependencies, and the relevant selector and coordinate
interfaces. Fresh isolated main and check builds both passed. No
mathematical gap or source correction was found.

The reviewed new implementation was authored by `controller_certificate`.
I authored the frozen cell-coordinate, cell-cycle and whole-field modules
and some earlier literal-table and alignment dependencies. This review is
independent of the new marked-window implementation; it is not a claim
that every dependency has independent authorship or was freshly replayed
as part of this packet. No reviewed or frozen source was edited.

## Source bindings

Paths are relative to `Computability/DiophantineConsistency/`.

| File | SHA-256 |
| --- | --- |
| `Lean/DiophantineConsistency/CurrentMarkedWindow2011.lean` | `b8df6733e6a812d31e251c817076671ce319927fd635731af3e88bab309585d3` |
| `Lean/DiophantineConsistency/CurrentMarkedWindow2011Checks.lean` | `0da5024cc6a44866be51dc659174e67c360bdfe753c3480eaba6b92bb1339ce6` |
| `reviews/current-marked-window2011-lean-author.md` | `852b3f85e70f97fcf6cf2ed7d40844b75288457645c50d6d9582a129ef74f58f` |
| `reviews/current-marked-window2011-lean-root.md` | `b9e07dc4366daf3102a7969053647ac46cd3aec3cbed19a0de1ffda998391f6e` |

Relevant exact direct dependencies:

| Module | SHA-256 |
| --- | --- |
| `CurrentOccupation2011` | `6b3d2cd7ec4c3f9380b63ee1211e6e93138f4f4e265aa9e1f8f83ddef01e6b5f` |
| `CurrentTileColors2011` | `c1f7fc6fda51795f182c0d14379206c781f8cdcae212e27ff5c0a9bede21b8f9` |
| `CurrentCellCoordinate2011` | `6e316a7a9a0107e8bc2bc41bf2bcd5868251b297f0b5cd7c79b64a52da1e9f48` |
| `WangTiles942Periodic` | `b426e06571ddc25095a0573784d2f289f116cb976468f826da128a4bb9713d53` |

## Mathematical audit

The definitions retain the exact original quantities:

```text
W = core.rank.toNat - 47*(N*2011)
s = (W/47)/2011.
```

The stride is not independently chosen or reduced modulo N. Its integer
cast is the stride supplied to the actual `MarkedWord` predicate.
The additional `NeZero N` instance is derived from the existing nonzero
physical modulus, with a low instance priority to avoid elaboration loops;
it is not an additional native premise.

`assignment` uses classical choice only to select the tile already proved
present in the original physical cell `coordinate.symm j`. The preserved
`Selected` predicate states that its original selector value is 1 and all
other abstract selectors in that same original cell are 0. It does not
construct a replacement Boolean word. The full occupation source inspected
here derives occupation from the original `Facts`: positive complemented
West transfers to successor East, contradicting the decoded empty case,
and the proved spatial cycle propagates from the forced Start.

At coordinate zero, `coordinate_symm_zero` identifies the physical origin.
`facts_start_selected` and uniqueness within that cell identify the chosen
tile as abstract Start 0. The module makes no assertion that Start occurs
at only one coordinate.

I checked both full-word source identities, including their signs:

- `coordinate.symm(j-1)` is the original physical predecessor.
- `coordinate.symm(j-s)` is the original temporal source at shift W/47.

These are exact identities in `ZMod (N*2011)`, so they retain wraparound
and arbitrarily large shifts. The second uses actual whole-field alignment
derived from the same `Facts`. Applying the actual selected-color theorems
therefore supplies precisely East(j)=West(j-1) and South(j)=North(j-s).
The integer cast used by `MarkedWord` is explicitly reconciled with the
natural quotient cast by `Int.cast_natCast`.

`facts_stride_nonzero` uses the actual Start color obstruction from
`CurrentTileColors2011`. Whole-field alignment gives `s*2011=W/47` as a
natural equality. The scaling lemma cancels 2011 in both representatives
and the modulus, so nonzero displacement in `ZMod (N*2011)` implies
nonzero stride in `ZMod N` without any coprimality condition. Positive
natural stride follows, since natural zero casts to zero. The singleton
coordinate remains mathematically valid, while actual one-cell `Facts`
are consequently impossible; the focused check verifies that distinction.

The `facts_marked_assignment` endpoint accepts only the original `Facts`
as native input and retains the full selector binding. `MarkedWindow`
keeps those same N, source x, c, carries and digits and augments them with
the assignment, actual `MarkedWord`, and exact stride conclusions.
`polynomial_zero_marked_window` starts only from positivity and zero
evaluation of the existing fixed polynomial and reuses the one original
arithmetic window; there is no resampling of its witnesses.

The focused signed-plane check also has the correct orientation:
address `-p-s*t` sends the east neighbor to cyclic predecessor and the next
time row to the temporal source. It uses the actual indexed table through
the concrete `WangTiles942Periodic.MarkedWord` structure, not an assumed
machine-semantic or target-equivalence property.

## Independent fresh replay

Both reviewed sources were hash-checked before running. The isolated
directory is `/tmp/current-marked-window2011-peer-9xbp3szs`. Dependency
objects were linked from the existing library, while both reviewed module
stems were excluded from those links. The main compiled to a fresh local
object, and the checks imported that exact object through the first
`LEAN_PATH` entry. Both shared objects remained byte-for-byte unchanged.

Both direct commands used Lean `v4.32.0`, `-M 6000 -j 1`, and each source
disables asynchronous elaboration. Both exited 0 on the first isolated
replay. The exact commands, paths, environment and before/after hashes
are recorded in the directory's `receipt.json`, SHA-256
`fd7fd391b8a7a291d1e636d1043d23f487b2f0afdf17325a814e80464943f4b3`.
The main diagnostics are empty, SHA-256
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
The checks log is SHA-256
`929bbec673e3855384ad1f13fd4b51074770bafa63cb7d46693939bd60052a7f`.
All nine axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

The fresh main object has SHA-256
`1f329d4981cd8b20b252ee0fbf34eeaa2f35d65fd47531eb89e601e95c696bb0`;
the fresh check object has SHA-256
`58e48d70e34353a5dea068e2c215e2e95f5874a8cfd06c2c97045866c67f9e1b`.
Both match the corresponding existing objects. This replay does not
rebuild the full dependency closure or the umbrella.

The accepted checkpoint is the actual polynomial-to-marked-cyclic-word
direction, with unchanged source binding and an exact positive nonzero
stride. Machine-run extraction, the reverse arithmetic construction and
an internal-ZFC consistency equivalence are outside this review's claim.
