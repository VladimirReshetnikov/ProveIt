# Cycle and helical marker construction: independent review

Date: 2026-10-26. Reviewer: `controller_certificate`. Result: **PASS**;
no source corrections requested.

Root authored the two new marker modules and their focused checks. I read
all four complete frozen sources before execution, together with the full
`TraceCycle`, `FinishConstruction`, and `WangMachineEncoding` sources and
the relevant helical definitions and proofs. My immediately preceding
independent review covered the entire helical quotient/extension packets.
I also previously independently reviewed `StepConstruction` and
`WangMachineTraceBounds`. I authored other arithmetic, marked-window, and
row-step modules in this project; none of those supplies a hypothesis or
direct import of these marker packets. This review does not claim a fresh
rebuild or independent authorship of the entire imported closure.

## Frozen files and bindings

Paths in this table are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942CycleMarker.lean` | 70 | 2385 | `2806b219857cfc334bc502fc15eccbebf0f6206a381c2e809029905e7d9076c5` |
| `WangTiles942CycleMarkerChecks.lean` | 40 | 1382 | `837a916c03a244f7ad535d1fa27e5fab0729beeb7c92d5b077bc746606822873` |
| `WangTiles942HelicalMarker.lean` | 60 | 2470 | `55962b759130f61cb138afde6a87796da4a12ddf7b0bc891a2d2417da2c788c7` |
| `WangTiles942HelicalMarkerChecks.lean` | 34 | 1457 | `e32e73c910ef7e6b676ce4a0c3e6d15ad7427f998bf81ba5082f6d7db090830b` |

CycleMarker imports only `WangTiles942TraceCycle`, source SHA-256
`58ca5b2877426faf6704700f970043526c50873f429e9248552d8bb3019ca17e`.
Its marker argument uses the literal initialization/reset rows in
`WangTiles942FinishConstruction`
(`b59a1698fdad679feb55bd6bb7a9eb440f46181204662f7245646522e403343d`)
and the actual encoded-color bound in `WangMachineEncoding`
(`0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e`).

HelicalMarker imports only `WangTiles942HelicalExtension`, source SHA-256
`1ca88d926e0002f2ee0eb7974176ebbe0f400c473e3b7ab742a44421b834bdc6`.
It uses the exact canonical-representative definition of `quotientWord`
from HelicalQuotient
(`dd7e2a20254aba54f57d03cc6690a6c18d3d45d83fe3c44383f53be4c3162481`).
Each check file imports only its corresponding main module.

## Mathematical scope and findings

`initialTile_north_start_iff` handles all signed spatial positions. The
initializer's north color is 435 exactly at zero; the left region has 434,
and the head/right regions have 436. The stronger tile equality follows
from this color criterion and the exact `initialTile_zero` identity.

For `cycleTile`, the initial row has precedence over the reset/finish
branches. Every noninitial reset row has north 438. Every other noninitial
branch, including a finish row that has not been proved allowed, has an
actual machine configuration's north color, bounded by 433. Consequently
`cycleTile k x = start` is equivalent to `k.val=0` and `x=0` for every
`k : Fin H`. No halt or height-lower-bound premise is hidden in this
argument. At height one it is still the initial branch; at height zero
there is no `Fin H` input. This local statement does not claim that those
small heights support valid temporal matching.

For the helical arithmetic helper, `representative w L (-x)=0` gives
`-x = w * quotient w L (-x)` by Euclidean integer division. The second
marker-coordinate condition makes that quotient divisible by `H`.
Therefore `w*H` divides `x`, and the explicit range `0 <= x < w*H`
forces `x=0`. This uses neither coprimality nor a sign restriction on the
quotient. The helper need not separately assume positive dimensions:
its range premise already excludes a zero product.

`quotientWord_marker_iff` applies that argument to the canonical `z.val`.
The quotient chooses actual tile indices only through band allowedness;
their exact tile value is supplied by `quotientWord_tile`. The local band
hypothesis explicitly states

```text
C x t = start iff x = 0 and t % H = 0.
```

It is used at the representative of `-z.val` and the corresponding signed
quotient time. Positive `w,H` supply the nonzero finite modulus; the
canonical representative has precisely the bounds needed by the helper.
Conversely, `0 <= L < w` puts the origin in the band, where the spatial
representative and time quotient are both zero.

The resulting theorem classifies the actual tile at each quotient
position as Start exactly at `z=0`. It requires allowedness and the
explicit local marker classification, with no horizontal or temporal
matching premise. Accordingly it does not by itself assert a `MarkedWord`,
derive the local classification for a completed computation band, or
construct a polynomial witness. It also does not introduce a global
unique-Start assumption into the earlier soundness direction.

Checks cover the height-one initial branch, negative spatial coordinates,
noninitial cycle rows, noncoprime dimensions, the complete local-to-quotient
marker statement, and a concrete counterexample if the canonical upper
bound is omitted: `x=12,w=3,H=4` has both marker-coordinate conditions but
is not zero. I found no circular premise or sign discrepancy.

## Fresh isolated replay

All four sources were compiled sequentially with Lean 4.32.0, `-M6000 -j1`,
and their own `Elab.async false` settings. The overlay at
`/tmp/wang-marker-construction-controller-peer/DiophantineConsistency`
excluded all four target stems, retaining symlinks only for existing
prerequisites. Both main objects were freshly created there before their
check files ran. No shared object was replaced. The command form was:

```sh
lake env bash -c 'export LEAN_PATH="/tmp/wang-marker-construction-controller-peer:$LEAN_PATH"; exec lean -M6000 -j1 SOURCE -o OVERLAY_OBJECT'
```

Every replay exited zero. Main modules emitted no Lean diagnostics. The
checks emitted four and two axiom reports, all using only `propext`,
`Classical.choice`, and `Quot.sound`. No reviewed source contains `sorry`,
`admit`, `native_decide`, or a new axiom.

| Replay | Seconds | Peak KiB | Fresh object SHA-256 |
| --- | ---: | ---: | --- |
| CycleMarker | 3.30 | 3192892 | `65bd7e99c2db66a76c25bd70d9a4f6a2b034c6e76eb49dcf1a4b432ed4332213` |
| CycleMarker checks | 3.11 | 3181304 | `1434daf78da36a08295bf2703ca7df6509acb8ee7b7388b52b34d914d9c39823` |
| HelicalMarker | 3.69 | 3202040 | `c49066562f370ba3ae84bdd2007c7336e37148960926be4650762161c111c75c` |
| HelicalMarker checks | 3.12 | 3180944 | `2ecb369f8654fa79d914706d2b68d01af7c5fc15f4d5ec483517c48b72a88914` |

Both fresh main objects are byte-identical to the pre-existing main
objects. There were no pre-existing check objects to compare. All four
review objects are regular files, not symlinks. All 31 recorded source,
object, and configuration inputs remained unchanged. The input manifest
`inputs-before.json` in the temporary directory has SHA-256
`9f1ed80ec072658ea6d95629da9f2087d6855b11543932e796c407358816ed72`;
the resulting `replay.json` has SHA-256
`6059145e6d8cf659d56061e01ba7515ded5e6300665180844e5bd7df8d8c86a6`.

The following log paths are relative to that directory. Logs include the
separate timing summary in addition to any Lean output.

| Log | SHA-256 |
| --- | --- |
| `cycle-main.log` | `14206ac46b0e71f22bbe6145f75ff9403681b7c1a7facfb6ce5f7a767a08decd` |
| `cycle-checks.log` | `61bb2b700b0332d5d52b22c6284ee332055b72d85e347745f595d0904fecbd31` |
| `helical-main.log` | `f4c6e8de8c5eae5f0a555af66a9ecadc53eff3f73dca18773f9f40d9cf44136a` |
| `helical-checks.log` | `e0b5f95c61a8097faca7dda4ca6fd22e528a8e2fb4c0236415e49d0accda9029` |

Only this assigned peer receipt was added. No frozen source, shared
documentation, or prerequisite object was changed, and no git operation
was run.
