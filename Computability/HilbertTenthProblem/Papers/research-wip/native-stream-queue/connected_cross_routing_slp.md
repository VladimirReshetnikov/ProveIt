# Complete paid evaluators for connected counter certificates

The connected report's horizon-indexed natural quadratic certificate admits a cheaper exact evaluator when its routing cross sum is factored. This prototype pays for the **entire original polynomial**: every shared affine form, every original residual, every residual square, the complete cross sum, and the final addition. It changes no coordinate, equation, coefficient or external-horizon convention.

For the report's two-counter transfer program at horizon 3, direct routing costs **245 operations**, column factoring costs **221**, and a shared row-complement form costs **206 = 65 multiplications + 141 additions/subtractions**. For the supplied five-branch, three-counter fixture at horizon 4, the complete cost falls from **840 to 456 = 129 multiplications + 327 additions/subtractions**. These are comparisons among explicitly emitted evaluators, not lower bounds or a fixed-arity universal equation.

Artifacts are the portable [compiler/checker](connected_cross_routing_slp.py) and [receipt](connected_cross_routing_slp.json). The receipt includes complete emitted gate lists for twenty representative packets, the original full linear row lists and direct cross terms, all interfaces, gate registers and phase ledgers. Other tested packets are deterministically reproduced by `build`.

## Exact retained source and public contract

The prototype authenticates the reference `well_conditioned_diophantine/src/substrate.py` at SHA-256

```
3dd949eae682c7b57d2c3ee9f8e86dad5d40c156a33d6010568868bc1b9173e4
```

before import and before every build, including when its private module cache is warm. Cold execution compiles the authenticated source bytes directly, so a timestamp-matching bytecode cache cannot override them. This is the original report source, not the separately repaired snapshot API. The prototype only calls its validated `Program` and `compile_certificate` interfaces and copies the returned data into its own packet. It neither calls the original aliased `export` API nor mutates the report.

The APIs are:

```
build(source, program, horizon, m=5, mode='row_diagonal')
checked(source, packet)
evaluate(source, packet, assignment, *, natural=True)
```

`source` is an explicit file path. `program` is an exact JSON dictionary with `dimension`, `start`, and an `instructions` list. Each instruction has exactly `op`, `counter`, `target`, `positive`; op is `INC`, `TEST` or `HALT`. Natural scalar fields reject floats and Booleans before constructing the original program. The original constraints include positive dimension, a nonempty finite instruction tuple with exactly one HALT, and valid targets and counters. The actual source accepts an exact odd `m≥3`, which this interface preserves; its connected-network interpretation additionally requires `m≥5`.

The four exact modes are `direct`, `column_diagonal`, `row_diagonal`, and `row_complement`. `checked` reconstructs the complete canonical packet and compares scalar and container types recursively. It rejects caller mutations of metadata, rows, gates, offsets and counts. It returns a fresh reconstruction. `evaluate` additionally requires exactly the declared parameter/witness names and exact integer values; `natural=True` requires nonnegative values. Signed evaluation is explicit with `natural=False`. Every build returns fresh nested objects; no public API returns the private module cache.

The source is a finite integer straight-line program with only binary `add`, `sub`, `mul` operations. Every emitted operation costs one. Multiplication by a nontrivial integer constant is charged. Literal constants and input wires are free. Exact constant folding and identities with 0 and 1 are applied; repeated literal operations use one cached gate. Subtraction is one addition/subtraction operation, including subtraction from zero when required. No division, exponentiation, comparison, summation macro or uncharged coefficient multiplication appears in an emitted source.

The emitter groups equal coefficients in an affine form and shares previously computed sums. In particular it computes the selector sum and each routed-column sum once before emitting the residuals which already require those sums. It charges these gates in `shared_routing_forms` in **every** mode, including direct routing. The ledger then records all linear rows, their squares, the sum of squares, the routing cross sum, and the final addition. Common-subexpression reuse, including any source-program-specific selector subset reuse, is reflected in the actual gate list.

## Full all-value identity

Fix a time step. Write `R` for the number of branches and `d` for the number of counters. Let

```
B = Σ_r b_r,
A_j = Σ_r a_rj,
A*_r = Σ_j a_rj.
```

These are derived arithmetic registers, not new witnesses. The direct cross polynomial is

```
C = Σ_j Σ_(r≠s) b_s a_rj.
```

Distribution in the polynomial ring over the integers gives, with no assumed residual or domain constraint,

```
C = Σ_j [B A_j − Σ_r b_r a_rj]
  = B (Σ_j A_j) − Σ_r b_r A*_r
  = Σ_r (B − b_r) A*_r.
```

These are respectively the column-diagonal, row-diagonal, and row-complement implementations. For `R≤1`, the direct polynomial is the empty zero sum and every factored implementation emits zero. For `R=2`, `B−b_r` is literally the other selector, so the complement mode uses that wire. For `R=3`, its two-selector sum is emitted as an affine sum and may share a source-state coefficient group. For larger R, it emits the paid subtraction `B−b_r`.

Every mode emits the same list of original affine residuals `ℓ_i`, and its complete output is

```
Σ_i ℓ_i² + Σ_t C_t.
```

Thus the output polynomials are **identical on every integer tuple**, not merely at previously typed zeros or after solving any source equation. There is no use of the selector constraint `B=1` or a routed-counter equation `A_j=c_j` to change the off-zero polynomial. In particular, replacing B by 1 would be invalid here.

Over naturals the original cross sum is a sum of nonnegative products. The factored expressions equal that sum even though their evaluation can have signed intermediate registers. The original first-halting and entire-witness uniqueness theorem therefore transfers unchanged. The theorem is not extended to unrestricted signed witnesses; only the polynomial identity has that larger scope.

If the program has Z test instructions, the unchanged source has

```
(d+3)(T+1) + 1 + T((d+1)R+Z)  natural witnesses,
d                                   natural input parameters,
d+5 + T(5+2d+2Z)                    affine residuals,
d R(R−1) T                         direct cross occurrences.
```

All forms have exact degree two: the original input-binding row contributes `x_j²` with positive coefficient and no other summand contains that parameter in a cancelling term. The source's initial constraints, final genuine HALT, routing guards, history, electrical rows, charge and terminal voltage normalization remain present. At T=0 there is no routing block; all four evaluators coincide. A program with no branches and T>0 retains its impossible selector row; the emitter does not silently accept early halting.

## What is saved, including the already needed sums

The shared residual/affine/square computation is identical across all four modes. For `R≥2` and `T>0`, the following are the additional routing-block costs including summation across time, but excluding the final one-gate addition to the already computed squared-residual sum:

| Routing schedule | Multiplications | Additions/subtractions |
|---|---:|---:|
| Direct | `TdR(R−1)` | `TdR(R−1)−1` |
| Column diagonal | `Td(R+1)` | `Td(R+1)−1` |
| Row diagonal | `T(R+1)` | `Td(R+1)−1` |
| Row complement, R≥4 | `TR` | `TR(d+1)−1` |

The row-diagonal count includes the new `R` row sums, each costing `d−1` additions, and the `d−1` additions combining the already available column sums. It also pays for every diagonal product and their sum. Compared with column factoring, it saves exactly `T(d−1)(R+1)` multiplications while using the same number of additions. This is a complete-source saving because the rest of the source is unchanged.

For `R≥4`, row complement saves one multiplication per time step relative to row diagonal but uses `R−d` more additions per time step. It is therefore cheaper in total when `d≥R`, ties when `d=R−1`, and is more expensive when `d<R−1`. For R=2 and R=3 the actual complement costs are lower than this generic formula because of the direct-other-selector identity or shared two-selector groups. The receipt counts those literal gates rather than applying an approximate formula.

Column factoring saves `Td(R²−2R−1)` of each operation type relative to direct routing. Hence it is already a strict saving for every R≥3, but for the report's R=2, d=1 countdown example it **increases** the complete cost by two operations per time step. Direct or row-complement routing is preferable there. These modes are not claimed globally optimal among arithmetic circuits; the finite census compares only these four emitted schedules.

Selected complete paid totals follow. Each cell is `multiplications + additions/subtractions = total` and includes every part of the source polynomial.

| Program and external horizon | Direct | Column diagonal | Row diagonal | Row complement |
|---|---:|---:|---:|---:|
| Countdown, d=1,R=2,T=3 | 48+85=133 | 51+88=139 | 51+88=139 | 48+85=133 |
| Transfer, d=2,R=3,T=3 | 92+153=245 | 80+141=221 | 68+141=209 | **65+141=206** |
| Five-branch fixture, d=3,R=5,T=4 | 345+495=840 | 177+327=504 | **129+327=456** | 125+335=460 |
| Eight-branch fixture, d=2,R=8,T=3 | 437+585=1022 | 155+303=458 | **128+303=431** | 125+321=446 |
| Four-branch fixture, d=6,R=4,T=3 | 309+455=764 | 183+329=512 | 108+329=437 | **105+323=428** |

The five-branch fixture is an explicit compiler stress input, not an instantiation of a universal machine or an asserted accepting trace. Symbolic identities and counts do not require it to halt.

## Checks and portable replay

The deterministic receipt records **20,455 checks**, including:

- 80 complete expanded polynomial identities from twenty program/horizon cases and four modes, and 224 more from the bounded R=2..8, d=1..8 census;
- 2,524 exact affine residual comparisons against the original compiler, exact degree and complete paid ledgers, and 15,262 acyclic exact-gate checks;
- 640 independent full-tuple evaluations, half signed, with the original energy evaluator;
- 32 original canonical natural zeros and 1,392 single-coordinate false-witness checks;
- exact saving-formula checks, 27 malformed-input or source-digest rejections, defensive-copy checks, a 150-digit integer fixture, and a cold forged-bytecode regression.

Symbolic equality is checked by an independent sparse integer polynomial expander over **every emitted gate**, then compared with a reconstruction from every literal source residual and direct cross occurrence. This does not depend on random evaluation or a schematic cross-only identity. The tests cover T=0, zero/one/two/many branches, nonzero initial state, both test branches, multiple counters, divergent programs, m=3 and m=5, and actual halting traces. The source authentication regression loads a private exact copy, warms the module cache, changes its file, and confirms that the next build rejects it.

Run from any directory:

```
python connected_cross_routing_slp.py \
  --source /path/to/well_conditioned_diophantine/src/substrate.py \
  --output new_connected_cross_routing_slp.json \
  --expect connected_cross_routing_slp.json
```

The expected receipt is compared with recursive exact types. The helper rejects `python -O` for its executable checking suite; public source/descriptor/assignment validation uses explicit exceptions. The prototype does not rerun the already-reviewed 38,524-check author suite, alter an archive or produce new author exports. All original rows and full polynomial values are instead verified directly for this evaluator change.

This is a paid arithmetic reduction for a finite external-horizon family. It does not compress unbounded support, select an unknown horizon within one fixed tuple, instantiate a universal counter program, or improve the maintained global 87-operation polynomial. Its useful transferable result is that row totals can be shared with an already paid selector/column interface to replace a quadratic-size routing evaluation by a linear-size one without changing even the off-zero polynomial.
