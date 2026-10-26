# Exact vertical boundary colors in the actual tile table

Date: 2026-10-26. Independent complete source/check review and fresh replay:
ROOT. See the [author receipt](wang-tiles942-boundary-author.md).

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| WangTiles942Boundary.lean (201 lines) | efda0078ffa174d2d9905cbd3431479a94679479742bbf9ff5856d132b06313c |
| WangTiles942BoundaryChecks.lean (84 lines) | 4a10236e6ec1943374ef076317f241c07955b3b9efde7325b8a55e8236a8586a |

Both complete frozen sources were read before fresh root direct
`lake env lean -M6000 -j1` runs. Main output went to a separate temporary
object; checks imported the frozen author-built object. Both passed, with
empty main diagnostics and fourteen standard-only axiom audits. No full
dependency or umbrella rebuild is claimed.

Exhaustive Allowed-family elimination distinguishes the boundary regime
from ordinary head colors: actual transition inputs are at most431,
actual receiver outputs include halt215 and are at most433. It follows
that north435 is exactly Start, north434 exactly initLeft, north436 exactly
initHead/initRight, and north438 exactly one of the three reset tuples.
South438 is exactly a finish tuple. Each reset output434/435/436 identifies
its exact reset tile.

North437 and south437 are equivalent and characterize exactly the nine
seam tuples(a^2,437,b,437), a,b in Fin3. Every such tuple also has an actual
indexed tile. The focused checks retain the sharp431 input bound, halt
outputs432/433 and initializer928 south4. They reject the old initializer
south188, forged seam west2 and a finish input in the boundary regime.

These statements are local to the exact finite table, with only Allowed
membership as premise. They neither derive a whole strip nor interpret
the finite finish constructor as halting semantics. Seam-column and
initialization-row geometry, actual run extraction, converse/controller
and internal-ZFC proof remain further work. The displayed decimal
equation and metrics are unchanged.
