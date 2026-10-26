# Grouped squares77/96: author proof, finite audit, and Lean replay

Status: PASS at initial freeze. I authored the two new Lean files and the
ordinary proof/graph/auditor packet. This is an author receipt, not an
independent peer review. No maintained page, umbrella, accepted proof, or
shared object was changed.

## Mathematical and source scope

The new polynomial is `(P*Q-1)^2+(U-1)^2+(Z-1)^2`, on the exact thirteen
positive coordinates and four current2011 ports of the accepted LV72
polynomial. The complete positive zero sets agree by identity witness maps.
The forward square implication uses integer nonnegativity only. The converse
uses the accepted positive parent norm theorem to derive `Z=U=1`, and then
the parent product equality gives `P*Q=1`; no separate sign conclusion for
`P` and `Q`, positivity of the signed ordinate, or canonical-witness premise
is added. The actual external `DiophantineConsistency.ConZFC` endpoint is
composed from the parent endpoint.

I fully read both new Lean files before compilation, their accepted parent
source/checks, the full parent auditor and literal graph, and the new ordinary
proof/auditor before running it. I read the entire generated 77-row graph.
The finite audit preserves all 69 prefix rows, proves the complete formal
tail identity, accounts for the sole main-norm leading cancellation by a full
323-term expansion, records every gate's full formal leader, and proves the
final specialized degree using the nonzero coefficient `256*beta^48`.
All 13 unknowns and 4 ports are live and have exact modular dependence
witnesses. All four complete ports were reconstructed and compared with the
copied gzip data. Raw size remains 47,313 bytes.

This is a degree/operation tradeoff, not a smaller operation count: 77 paid
binary operations versus 72, degree96 versus124. The finite degree result is
not itself a Lean theorem. Neither this packet nor the reused external
consistency endpoint proves an internal HA, PA, or ZFC consistency statement.
No complete arithmetized C222 checker/runtime equivalence is claimed.

## Frozen files

| File | SHA-256 |
|---|---|
| `Lean/DiophantineConsistency/ThirteenGroupedSquares96.lean` (134 lines) | `1b9aca9cb96c390ab074001c36680567969c6a33b6e556798b8394500d3cd424` |
| `Lean/DiophantineConsistency/ThirteenGroupedSquares96Checks.lean` (48 lines) | `07e79a6a7382e84a151e194ccae0d3a5494d17cfab8f679d5904a538ba9bb24a` |
| `research/thirteen-grouped-squares96/PROOF.md` (147 lines) | `6f2a4e7376dc05772fd98f7753f61ca9bf9c5081eb218a769da12d85ae7bf895` |
| `research/thirteen-grouped-squares96/audit.py` (401 lines) | `2b656fd647f284edceb22068748c08020b6a5bab4ef0af0469104f0be8795801` |
| `research/thirteen-grouped-squares96/polynomial.json` | `05710557a8029ebdb378a6ac156f25e79b848eb10e673c01008acb415fc3e39d` |
| `research/thirteen-grouped-squares96/CERTIFICATE.json` | `9f224ce9b83e9f2900238131df536e9b0034bb0daf5a65adbabb0c72357ea923` |

All paths in this table are relative to `Computability/DiophantineConsistency`.

## Exact replay and cache boundary

Private output directory:
`/tmp/thirteen-grouped96-author-9b5lvaoc`.
It links the 449 `.olean` entries in the previously accepted root LV overlay
`/tmp/thirteen-lv-root-peer-ox84rr2w`. Every resolved object hash was observed
before and after the new leaf builds and remained unchanged. The direct
parent source is
`d64e31b377007ddd05964e29a1976c857d036d6eb919524df58c3bd8c237bd02`;
its reused object is
`659a14b08545874c8b667037008b6d0b798bffce0a66114aceebe9eb60018086`.
This records the authorized frozen-LV cache reuse; it does not retroactively
authenticate that cache as a freshly rebuilt postmerge transitive closure.
Standard package objects and the normal Lake fallback search path were
retained. No Foundation or package object was rebuilt.

The final two commands used `lake env bash`, then prepended the private
directory to `LEAN_PATH` inside that shell and invoked:

```sh
lean -M6000 -j1 -DElab.async=false -o PRIVATE/DiophantineConsistency/ThirteenGroupedSquares96.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenGroupedSquares96.lean
lean -M6000 -j1 -DElab.async=false -o PRIVATE/DiophantineConsistency/ThirteenGroupedSquares96Checks.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenGroupedSquares96Checks.lean
```

Both exited0. Main:5.83s, peak3,386,344KB, empty diagnostic log.
Checks:3.00s, peak3,364,980KB, all nine axiom reports restricted to
`propext`, `Classical.choice`, `Quot.sound`.
The fresh object hashes are respectively
`b6135b0cfa90a88101dd80d602154140252db6932079c539d9a818ee6b91dfa9`
and `14d5ec5655503dac6d228019b113fc987f021f85d6dbbb7ca1f47b606cc14b54`.

The initial main attempt failed only on an unavailable `pow_eq_zero` name
and tuple tactic indentation; explicit `nlinarith` consequences and `refine`
fixed those. The initial checks found an inherited `auxiliary` name ambiguity;
the new definition was fully qualified. All failed logs are retained, and no
mathematical statement or domain was weakened. No source edits followed the
final successful builds.

The finite auditor's `--write`, default, and `python3 -O` invocations all
exited0 and reproduced the same deterministic certificate. It uses explicit
`require` guards, imports only the Python standard library, and never executes
the parent auditor or incoming code. The generated packet remains separate
from the current display.

The complete durable pins, 449 prerequisite observations, successful and
development logs, timing files, and exact replay commands are in
[thirteen-grouped-squares96-replay/REPLAY.json](thirteen-grouped-squares96-replay/REPLAY.json),
SHA-256 `deb252941de4ebb4e079cf01fc8b22715f6246edfeeb065fcd95f08c2595115b`.
