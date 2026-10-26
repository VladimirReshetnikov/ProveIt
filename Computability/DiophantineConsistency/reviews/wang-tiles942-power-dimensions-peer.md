# Actual power dimensions: independent peer review

Date: 2026-10-26. Reviewer: `controller_certificate`. Author: root.
Result: **PASS**, no requested changes.

## Frozen source bindings

Paths are relative to
`Computability/DiophantineConsistency/Lean/DiophantineConsistency/`.

| Source | Lines | Bytes | SHA-256 |
| --- | ---: | ---: | --- |
| `WangTiles942PowerDimensions.lean` | 64 | 3067 | `1021a39e8106c9a493986ee72aa0d2f85addff0a2d3ee822ca44a8a6441ae283` |
| `WangTiles942PowerDimensionsChecks.lean` | 51 | 2322 | `89ec6c7ca99cecb41fed606f4db6a455589fd5f0b626330924e5265d70275c25` |

I read both complete sources before execution. I also read the full
direct dependencies `WangTiles942Completeness` and
`WangTiles942BandMarker`, followed their actual canonical construction
through `CycleBand`, `CycleBoundary`, `TraceCycle`, `CycleMarker` and
`HelicalMarker`, and inspected the pinned Lean proof of
`Nat.lt_pow_self`. The helical quotient and extension had already
received my separate full-source independent review.

I authored none of these geometric construction modules. I authored
the earlier `WangTiles942RowStep` and `DecimalMachineZFC` modules that
occur transitively through the imported completeness module's
soundness/calibration side. The new proofs here use only its elementary
`width_split` and the independently authored constructive band-marker
interface; they do not invoke that soundness direction or consistency
calibration. This receipt is independent review of the new dimension
composition, not a claim of independent authorship of every transitive
module.

## Mathematical and interface review

`cofinal_unique_marked_word` takes an actual halting time, width at least
`2*T+4`, and height at least `T+2` and3. It sets the left margin to
`T+2` and allocates the remaining width to the right. The natural
subtraction is justified by the width hypothesis, yielding the exact
sum of margins and both required margin bounds. After substitution,
the marked property and unique-Start property are extracted from the
same explicit `canonicalWord` of the actual band. Uniqueness is not an
extra premise or a property borrowed from a different existential word.

The direct band-marker interface has already discharged local Start
classification, seam exclusion, actual942-tile injectivity, and helical
quotient preservation. Its matching uses the signed address and the
twisted seam, so width and height need no coprimality condition. The
new specialization preserves the actual positive product modulus
`w*H` and stride `w` exactly.

`exists_power_dimensions` chooses explicit positive exponents

```text
rw = 2*T + wBound + 5,   rh = T + hBound + 5.
```

For any natural `p>1`, `n<p^n` gives the trace-margin requirements and
the two strict external lower bounds. Each exponent depends on its own
dimension bound; no comparison between width and height is introduced.
The arithmetic theorem is unconditional in `T`, and does not itself
assert a halt. In particular the composite-base and `T=0` checks are
legitimate arithmetic examples. The separate base-one negative control
correctly shows why `p>1` is necessary.

`exists_power_marked_word` combines the dimension witnesses with the
actual halt. Its finite word still has type `ZMod (p^rw*p^rh) → Fin942`.
The equality `p^rw*p^rh=p^(rw+rh)` is returned explicitly by `pow_add`;
there is no hidden dependent-type transport replacing the word or
silently changing a modulus instance. The nonzero product instance is
proved from `p>1`. Both matching and the exact index-zero marker
equivalence remain attached to that same word.

The checks reproduce the fully quantified endpoint, specialize the
eventual auxiliary base120199 without asserting its primality, and
preserve independent bounds and the exact product modulus. This packet
proves neither a power-orbit theorem nor CRT, safe dummy placement,
controller arithmetic, or a Diophantine solution. Its stated scope is
accurate.

## Fresh isolated replay

Both targets were rebuilt sequentially in
`/tmp/wang-power-dimensions-controller-peer/`, excluding both reviewed
target stems from the dependency overlay. The checks imported the
fresh main. Commands used `-M6000 -j1`, the source's `Elab.async false`,
and pinned Lean4.32.0. Existing dependency objects were reused; this is
not a fresh transitive-closure replay.

Main: PASS,3.17seconds, peak3269400KiB, no Lean diagnostics.
Checks: PASS,2.91seconds, peak3257812KiB, three standard-only reports.
All reported axioms are `propext`, `Classical.choice`, `Quot.sound`.
Neither source contains `sorry`, `admit`, `native_decide`, or an added
axiom. Both fresh objects are byte-identical to the original objects.
Twenty-seven selected source/object/toolchain/manifest inputs were
reauthenticated unchanged after replay.

| Isolated evidence | SHA-256 |
| --- | --- |
| `inputs-before.json` | `c1f0edfbff1695eb87c17973bade79b1162b58f5302d10e66a3368ea4bd5ed24` |
| `main.log` | `388ed4f389c6ea0c04f005dccb5df21c258a7b3096c3b697b69ac87cca242d1b` |
| `checks.log` | `6d21f8a8fcf68783ec4682bd16b7a17f68f8edee1c83f620b6cb0f6f22666841` |
| Main `.olean` | `10c0788be4c85e0d5951ddd4e6c846c8a5a60c75f4c6e24c73aeb9eb60f02545` |
| Checks `.olean` | `454a7977c15748e54e683b9a0d1f5a9a6d49a7e2e0bb17f7498f59abb48b74be` |
| `results.json` | `a412b2b21101720420aa5235fdcbac473702fdedf4982e28126161ff6b58c5f2` |

Only this new peer receipt was added. No reviewed source, shared object
or shared document was edited, and no git operation was run.
