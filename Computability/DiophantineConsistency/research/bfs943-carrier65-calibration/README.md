# iPRA endpoints for the Carrier65 polynomial at the direct-BFS943 ports

The Carrier65 polynomial (package 183's `equation/carrier65.json`: fourteen
positive unknowns `J, F, α, z, f, i, T, s, w, n, η, ζ, y, γ`, 65 operations,
exact degree 150) is the parent of package 170's quotient carriers. Its Lean
literal `ObjectCurrentEquation2011.expressionAt` is port-parametric and was
already calibrated at the block-mask2963 and admissible942 tuples
(`research/block-mask2963-calibration`, `Adm942/IPRACarrier65Adm942`). This
record calibrates it at the direct-BFS943 ports of `IPRATrace75`,

  `fixedPorts = ![β, K0, MC, β + MF_native]`

(β = 2^590069 − 1, raw hashes K0 `0a86821a…`, MC `6007cabd…`, MF `48333b0d…`,
β `0664a868…`; package 170's `compact/COEFFICIENTS.json` names the same four
raw hashes, which `check_lean_graph.py` verifies).

The endpoints are in `Lean/DiophantineConsistency/BFS943/IPRACarrier65BFS943.lean`
(namespace `DiophantineConsistency.IPRACarrier65BFS943`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, with
`expression : Expr (Fin 14)` and
`expression_def : expression = ObjectCurrentEquation2011.expressionAt (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

**Soundness** (`Carrier65BFSSource`). The port-generic
`ArithmeticCarrierSoundness2011.expressionAt_equations` turns a positive zero
into Carrier65's five additive equations (transport unit, first, main, strong
and auxiliary norms, with the carrier `τ = E n + k - R`). At ports with
`31 ≤ β`, `MC < β`, `MF < 2β` and `β + 1 = 2^d` these give the four fields of
`BFS943FixedSource.FixedSource` at `sourceVal u = ![J, F, α, 1, 1, w, 1, 1, 1, 1]`:
`w q = 2^R` (`ArithmeticPellPowerRecovery.maintained_power`), the mask
`F + α < q` (`ArithmeticPellFirstIndex.scalar_window`), the natural transport
`(K0 + w) C = F + h (z - 1)`, and `q = 2^ℓ` (`factor_alignment`) with
`3ℓ + 2 ≤ population R` (the body of `Bm2963HalfBinomial.population_of_equations`,
restated over arbitrary ports: `maintained_first_indices`,
`ArithmeticHalfBinomial.half_binomial`, `population_lower`,
`rank_lower_of_radix`). `FixedSourceHalt.source_halts` then gives halting
(`equations_halt`, `zero_halts`). The port bounds are
`Trace75FixedBounds.fixed_bounds`.

**Completeness** (`Carrier65BFSHalt`). `DirectBFSHaltPellSeed.halt_seeds_transport`
gives the direct-BFS943 halting packing, its rank `R`, the outer Pell seed
(`ArithmeticOuterSeed.SeedRelations`), `q w = 2^R` and the transport quotient
`t`. In Carrier65 coordinates (`halt_outer`): `J = rep d N`, `F`, `α` of the
packing, `q = 2^(dN)` (`β J + 1 = q` by the repunit identity), the packing rank
is literally the Carrier65 rank formula at `MC = low`, `MF = high + β`,
`R ≡ 3 (mod 4)` (`CompactRankResidueJoin.properties`), and the transport unit
holds with `z = t + 1`. `halt_equations` adds the auxiliary seed
`ArithmeticPellAuxiliarySeed.auxiliary_seed` and assembles the five equations
(`ArithmeticConstructionAssembly.equations_of`); `halt_zero` gives the literal
zero (`ArithmeticConstructionZero.equations_zero`). The ports' model values are
`port_values` (`CompactSymbolicBetaCast.beta_model`,
`CompactSymbolicMaskData.low_eq`/`high_eq`). `halt_outer` is stated separately
because package 170's carriers reuse it with a different strong multiplier.

No new cell decoding or packing layer is needed: unlike the block-mask2963 and
admissible942 calibrations, the direct-BFS943 word layer is reached through the
zero-free `FixedSource` boundary, and the halting packing is the existing
direct-BFS943 one.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins
package 183's `carrier65.json` (`bf58ed66…`), package 163's
`trace75_degree402.json` (`8b9b9421…`) and package 170's `COEFFICIENTS.json`
(`0fe6f625…`). It checks the circuit metadata (fourteen witnesses in the Lean
order, ports `beta, K0, MC, MF`, 65 operations, degree 150, no dead rows), that
package 170's four raw port hashes equal the direct-BFS943 ones of the 75 graph,
parses every `let` row and the output of `expressionAt` into the same interned
DAG as the JSON rows, and compares after exact commutative-ring structural
normalization (no distribution): the output and the rows `rank`, `tau`, the
first, main, auxiliary and scaled strong norms, the transport, `V`, `S` and
`Δ`. It rejects 12 single-gate mutations of the Lean text and checks the
endpoint's `fixedPorts` (textually the `IPRATrace75` one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers it),
`expression` and `expression_def`. Output: `check-output.json`. The circuit
file carries package 183's admissible942 coefficient tuple; only its arithmetic
program is compared, and the endpoint's ports are the direct-BFS943 ones.
These are finite external checks, not Lean theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Carrier65BFSSource` | `sourceVal`, `source_of_equations`, `source_of_zero`, `equations_halt`, `zero_halts` |
| `Carrier65BFSHalt` | `PortValues`, `port_values`, `halt_outer`, `halt_equations`, `halt_zero` |
| `IPRACarrier65BFS943` | the iPRA endpoints |

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. No new `maxHeartbeats` raise is used (the modules run at the default).
Nothing is claimed about package 183's admissible942 coefficient payloads or
about minimality.
