# Controller-shaped actual marked words: author receipt

Author: `complemented47_review`. Both new modules are frozen after a
complete source/check self-read and successful first capped builds.
This is an author receipt, not an independent review.

| New source | SHA-256 |
|---|---|
| `WangTiles942ControllerDimensions.lean` (96 lines) | `ffdb29e9f5048c6a47bc63dc17276d709fa0ac44d854b6115d8797c884346425` |
| `WangTiles942ControllerDimensionsChecks.lean` (55 lines) | `ec6a4bb4310be1deb2543771c0069820bce910f304df8ffc30b530e5226f10b6` |

The module imports exactly `WangTiles942PowerDimensions` and
`CurrentControllerData2011`. I read both complete sources, the complete
periodic MarkedWord definition and Completeness endpoint, and the full
canonical BandMarker source before constructing the wrapper. All Lean
source paths here are under `Lean/DiophantineConsistency/`, relative to
`Computability/DiophantineConsistency/`.

| Relevant frozen prerequisite | SHA-256 |
|---|---|
| `WangTiles942PowerDimensions.lean` | `1021a39e8106c9a493986ee72aa0d2f85addff0a2d3ee822ca44a8a6441ae283` |
| `CurrentControllerData2011.lean` | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` |
| `WangTiles942BandMarker.lean` | `4fe8030da31229c7758c9c1c4f73c1443fe1881875a34990adb8817fbf827cb4` |
| `WangTiles942Completeness.lean` | `fcddd37eb2cec2e11c6845226839c0ea557d9edd17175d1c60d7b4f46ec21615` |

`transportWord h a` is dependent equality transport of the supplied a,
where h proves equality of the complete natural moduli. The accompanying
generic theorem proves both literal matching equations and unique index
zero for this very transported word. It has explicit nonzero instances on
both moduli and is proved by equality elimination. It assumes neither a
new word nor a desired factorization of a plane.

`exists_controller_dimensions T wBound hBound hh` invokes the accepted
actual halting-word construction with width bound wBound and height bound
`max hBound auxiliary^2`. Its only non-arithmetic input is the literal
machine's halting-time equality hh. The constructed height power is
strictly greater than auxiliary squared, hence its exponent rh is at least3.
The width exponent rw is positive. Defining k=rw+rh-1 then gives k+1=rw+rh,
rw<k and k>=2. The fixed inequality d<auxiliary implies
`d*auxiliary < auxiliary^2 <= auxiliary^k`.

The existing exact product identity
`auxiliary^rw * auxiliary^rh = auxiliary^(rw+rh)` supplies the modulus
equality. The construction retains the word obtained from the actual
canonical band, its unique Start, and its original temporal stride
auxiliary^rw. The endpoint exposes k, rw and rh, both independent strict
cofinal bounds, every controller exponent inequality, and the actual
MarkedWord on `ZMod(auxiliary^(k+1))`. Nonzero modulus proofs are explicit.
The smaller `exists_controller_marked_word` wrapper forgets rh and the
unused height bound while retaining the word and unique Start.

No primality, coprimality, power orbit, safe subset, rank calibration,
ordinary mutation, or equation solution is an input to this construction.
The imported auxiliary is the actual120199, and d is94517. This packet
closes the geometry/controller dimension mismatch; it does not alone
prove the equation converse.

Focused checks retain the supplied word through transport, identity
transport, strict-height necessity, the arithmetic lower exponent pair
rw=1/rh=3, the full two-bound endpoint, and the smaller controller interface.
The arithmetic boundary examples do not assert a machine halt. All five
axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
There are no new axioms, `sorry`, or `native_decide`.

Both sources set `Elab.async false`. From the repository root I ran
`lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/<name>.olean
Computability/DiophantineConsistency/Lean/DiophantineConsistency/<name>.lean`
sequentially, under `/usr/bin/time`, redirecting to the logs below. Main
passed in3.17seconds with peak RSS3,320,316KiB; checks passed in2.91seconds
with peak RSS3,310,192KiB. Main has an empty log; checks contain only the
five axiom reports. No implementation correction or retry was needed.

| Build artifact | SHA-256 |
|---|---|
| Main object | `dc79dfe395bfd48bc2f534d9777125d81c020e3fc29307be2bd21640fcaae926` |
| Checks object | `c15fd02e5a5cf1786e2643276a940a305d835d3812b8e124d2d8a0b0fe2ee111` |
| `/tmp/wang-controller-dimensions-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/wang-controller-dimensions-checks.log` | `27d568210f00a043becf22b118b811bcefe613923acdac0341424fad81fbedc2` |

Only these new sources/checks, their new objects, this receipt, and temporary
build logs were written. No accepted dependency, umbrella, central document,
or Git state was modified. Root review and independent replay remain separate.
