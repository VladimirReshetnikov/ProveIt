# Actual-rank composition

`FreeMainRankedMain.main_at_rank` identifies the main Pell coordinates at the
actual graph rank `R`. It assumes an IΣ₁ model, natural ports, an actual
positive zero of the 72-operation graph, `q ≥ 33`, `0 < R`, and `2R < c`.
The proof composes the checked conditional half-index bridge with the checked
natural strong and auxiliary norm identities extracted from that zero. The
rank inequalities remain explicit premises: this does not prove the reverse
witness map, an equivalence with the 76-operation graph, or an iPRA endpoint.
The historical source header says “Unchecked draft”; the successful check
below is the actual status of those source bytes.

Attempt03 passed with Lean exit 0, one expected axiom report
`[propext, Classical.choice, Quot.sound]`, no warnings or `sorryAx`, and stable
direct input guards. Its retained log and receipt are in
`observations/attempt03/`. The output object remains at
`/tmp/p64-qcube72-ranked-main-priority-check03/FreeMainRankedMain.olean`.

| Artifact | SHA-256 |
| --- | --- |
| `FreeMainRankedMain.lean` | `633f9b3d64fee060a845e18c1d1a437137c08d06ac55232c3ebb232651d65a3f` |
| `check03.py` | `b78fc2608dbbc03cecbfc5a0eb44c342add76c9ef324ae1e49deae76ddc6cc55` |
| `observations/attempt03/compile.log` | `4b8b64378605248fe8e1bfa678be0d7ca39ff6e7f9bba88cbc6111bc3c8c0a98` |
| `observations/attempt03/result.json` | `476ea25cd88141f0a8ab0832af5740636423fa93df8eee00ffdb0b9c41dd0eaa` |
| Output object | `be2865b509d0f2f854430a3ce10dd2f6e6474b0e9801988661349236a60c40e8` |

The runner guards the source, Lean executable, and the direct
`FreeMainConditionalRank` and `FreeMainAuxNorm` provider objects. The check
uses a 2,400 MiB Lean limit, 120-second timeout, sampled process-group RSS
limit of 3.5 GiB, minimum 10 GiB available host memory, and low CPU and I/O
priority. It inherits the providers' transitive and dynamic ancestry and
samples resource use, so this is not a source-only rebuild.

Attempts 01 and 02 failed on layout/parsing of a local `let` in the `change`
expression; neither produced an object, and each report contains `sorryAx`
from the error. Their exact source snapshots, runners, logs and receipts are
preserved under `observations/attempt01/` and `observations/attempt02/`. The
successful source spells out the absolute-difference term instead.
