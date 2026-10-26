# Author receipt: exact boundary-color classification

Status: frozen; complete self-review and fresh bounded Lean module/check
compilation PASS. This is an author receipt, not an independent review.
The only mathematical hypothesis of the classification lemmas is membership
in the exact finite `WangTiles942Language.Allowed` language.

Paths are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
|---|---:|---|
| `Lean/DiophantineConsistency/WangTiles942Boundary.lean` | 201 | `efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c` |
| `Lean/DiophantineConsistency/WangTiles942BoundaryChecks.lean` | 84 | `4a10236e6ec1943374ef076317f241c07955b3b9efde7325b8a55e8236a8586a` |

The sole direct import is `DiophantineConsistency.WangTiles942Language`,
source SHA-256 `a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d`.
The new object `.lake/build/lib/lean/DiophantineConsistency/WangTiles942Boundary.olean`
has SHA-256 `724169439dc061e2fde82d7645ebe8fdde85d754c946070c5e4ac34931a4cc9c`.
No frozen source, machine data, coefficient, equation, or prerequisite
object was edited or rebuilt. No commit was made.

## Proved local classifications

The two exhaustive elimination lemmas `high_north_cases` and
`high_south_cases` account for every constructor of the actual finite
language. Their arithmetic exclusions distinguish transition input heads
from receiving output heads:

- For `j : Fin 430`, the input head is `2*(j/2)+(j%2)+2 ≤ 431`.
  No transition out of the halt state is introduced.
- For an actual direction-specific target `q` and `b : Fin 2`,
  `headColor q b ≤ 433`. This uses the actual proved target bound `q < 216`,
  retaining `q = 215` and its head colors 432 and 433.
- A plain/halt pass or finish input color `432*a+b` is at most 433.

For an allowed tile `t`, the exact equivalences are:

| Color condition | Exact tile description |
|---|---|
| `north = 435` | Start `(2,435,3,1)` |
| `north = 434` | initLeft `(2,434,2,0)` |
| `north = 436` | initHead `(3,436,4,4)` or initRight `(4,436,4,0)` |
| `north = 438` | `(1,438,1,p)` with `p` in `[434,435,436]` |
| `south = 438` | `(0,432*a+b,0,438)` with `a,b : Fin 2` |
| `north = 437` | `(a²,437,b,437)` with `a,b : Fin 3` |
| `south = 437` | The same nine seam combinations |
| `south = p`, for `p` in `[434,435,436]` | Exactly `(1,438,1,p)` |

Consequently `north = 437` iff `south = 437`. `seam_tile_exists`
additionally recovers an actual indexed tile for each of the nine finite
seam combinations through the exact `allowed_iff_tile` theorem.

All statements are local to a single tile. No adjacency, strip,
periodicity, run, blank initialization of a whole row, halting, or
Con(ZFC) hypothesis or equivalence is asserted. In particular, the word
“finish” denotes the literal finite constructor, not a proved halting
semantics.

## Focused checks

The checks cover the sharp last transition head 431, the retained halt
heads 432/433, the actual indexed initializer 928 with south color 4,
the three exact reset south colors, seam membership and seam equivalence,
and Start classification at every actual tile index.

Three negative checks reject:

1. `(3,436,4,188)`, the old initializer's head color in the current table;
2. `(2,437,0,437)`, because seam west colors are squares 0, 1, 4;
3. `(0,434,0,438)`, because a finish input is only a plain/halt color.

All source and check lines were read. Initial elaboration corrections
made structure-field reductions explicit before arithmetic reasoning and
set a bounded recursion limit; no statement or mathematical premise was
weakened. The final comment clarifies that reset classification is local.

## Fresh checks and axioms

From the repository root, using Lean `v4.32.0` and `Elab.async false`:

```sh
lake env lean -M6000 -j1 \
  -o .lake/build/lib/lean/DiophantineConsistency/WangTiles942Boundary.olean \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942Boundary.lean
lake env lean -M6000 -j1 \
  Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangTiles942BoundaryChecks.lean
```

Final main PASS: 3.98 seconds, peak RSS 3,203,300 KB. Final checks PASS:
6.28 seconds, peak RSS 3,673,416 KB. Logs:
`/tmp/wang-boundary-main.log` and `/tmp/wang-boundary-checks.log`.
Timing is from `/usr/bin/time`. Existing prerequisite objects were reused;
this receipt does not claim a fresh replay of their full closure.

All fourteen reported endpoint dependencies contain only `propext`,
`Classical.choice`, and `Quot.sound`. There are no warnings, `sorry`, new
axioms, or `native_decide`.
