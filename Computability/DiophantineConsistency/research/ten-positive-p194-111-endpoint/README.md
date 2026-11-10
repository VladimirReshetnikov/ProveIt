# iPRA endpoints for package 194's ten-positive 111/198 `product2` circuit

Package 194 (`con-zfc-diophantine-forms/194-guarded-resultants-early-projection`)
supplies, in `positive/`, three root-scale centred versions of package 172's
87/214 free-inverse chart (proof: `positive/PROOF.md` §§1–6). This record
covers `product2_radix67.json` (mode `product2`, 111 operations, exact degree
198, weight `L = bV`, root scale `r = 2`). The shared root-scale-two layer
(`Scaled87*`) is recorded with the companion 97/202 `quotient_t` circuit in
`research/ten-positive-p194-97-endpoint`. Only the `_radix67` copy is on the
direct-BFS943 tuple; the `_low2963` copy is a different tuple.

In the notation of `research/ten-positive-p172-87-endpoint` (the Lean register
`Y = q s` is package 194's `Ybar`, `Am1 = A - 1`, `X Y² k = ell`), the circuit

* replaces the 87 transport gate `n - b V B` by `(n - b V B) - Ω₂` at the
  first-product centre
  `Ω₂ = U {2A [E V - θ (E² + S²)] + S [4 θ E - (b - c)]}`,
  `S = (k Ybar) [ell + k - (k Ybar) (Ybar + 1)]`, `θ = U² b`
  (JSON rows `cy`, `Yp1`, `cyYp1`, `sinner`, `S`, `U2`, `theta`, `thetaE`,
  `fourthetaE`, `bmc`, `Rc`, `E2`, `S2`, `Sc`, `EV`, `thetaSc`, `Vdiff`, `twoA`,
  `Apart`, `SRc`, `whole_inner`, `Omega`, `raw_center`, `center`), so
  `Z = Z₈₇ - M Ω₂`;
* replaces `G` by `4 G` in the norm (rows `scaledG`, `RG`):
  `P = Q (Z² - 4 M² G V²) + (4 M² G - Z²)`.

The `coefficient_binding` equals the 75/402 graph's in every port field except
the relative `path` and an explicit `endianness: little` annotation: the
direct-BFS943 tuple, K0 raw `0a86821a…`, MC `6007cabd…`, MF `48333b0d…`,
β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace111.lean`
(namespace `DiophantineConsistency.IPRATrace111`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`, with `expression_def :
expression = TenPositiveTrace111.expression (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

As for 97/202 (see that record): the root scale is removed by parity
(`Scaled87Sign.even_of_sq`, `Q - 1` odd), `Scaled87Sign.shift_zero` turns a
positive zero with a shift satisfying `Ω₂ ≤ 5 g |V|` into
`Trace87ShiftTransport.ShiftZero p v (Ω₂ + z)`, the shifted 87 chain
(`Trace87Shift*`) gives `BFS943FixedSource.FixedSource`, and
`FixedSourceHalt.source_halts` gives halting; completeness is
`Scaled87Complete.scaled_zero` at the natural shift `Ω₂`.

**The centre** (`Trace111Estimate`, `Trace111Omega`). Package 194 §4 bounds
`Ω₂` through the polynomial quotients `Q_j` of `E(T) V(T)` by `T^j`. The Lean
proof does not use those quotients; it bounds the literal evaluator directly,
which suffices because only the crude bound `Ω₂ ≤ 5 g |V|` is consumed.
At positive inputs, with `X ≥ q ≥ 2`,
`S = k² Ybar ((X - 2) Ybar² + Ybar (Ybar - 1) + 1)` and
`E - S = 1 + k² (X Ybar³ (X Ybar - 1) + X Ybar² + Ybar³ + Ybar (Ybar - 1))`,
so `0 ≤ S ≤ E` (`Trace111Omega.omega_data`). In the scalar form
`Ω = U (2A (E V - U² b (E² + S²)) + S (4 U² b E - (b - c)))`,
`V = (1 + 2 (A² - 1) U² E) b - c`, `0 < c ≤ U`, `A ≥ 2`:

* `omega_upper`: `Ω ≤ 3 A U E |V|` for every integer `b` (cases `b ≥ 1`:
  `4 U² b E + c ≤ A V`; `b = 0`: `Ω = U c (S - 2 A E) ≤ 0`; `b ≤ -1`:
  `4 A U³ E² |b| + U E (|b| + c) ≤ 5 A U E |V|`);
* `three_lt_five`: `25 G - 9 (A U E)² = 25 E + (U E)² (16 A² - 25) > 0`, so
  `3 A U E < 5 g`, giving `omega_shift` (`Ω₂ ≤ 5 g |V|`);
* `omega_nonneg`: `Ω ≥ 0` once `b ≥ 1`; at the 87 zero `V > 0`
  (`Centred87Complete.V_positive`), hence `b > 0`, so the completeness shift
  `Ω₂` is a natural.

`Trace111ModelIff.positive_model_iff` joins both directions; the iPRA wrappers
are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
111 JSON, package 172's 87 JSON (also checking the JSON's `parent.sha256`), the
75 JSON (port binding), the 87 record's checker (whose parser and normalizer
it imports) and the Lean sources that checker reads (`TenPositiveTrace75.lean`,
`Trace79Regs.lean`, `Trace82Regs.lean`, `Trace87Regs.lean`). It checks the
graph metadata (including `root_scale: 2`) and that the JSON rows differ from
the 87 rows exactly by the centre, transport and `4 G` gates; transcribes
`value87` with the 87 checker (re-checked against the 87 JSON), then parses
`omega` (with its lets `S`, `theta`), `TenPositiveScaled87.regsW` and
`value111` into the same interned DAG and compares with the JSON output after
exact commutative-ring structural normalization (also the rows `S`, `theta`,
`Rc`, `Sc`, `Vdiff`, `Omega`, `raw_center`, `center`, `scaledG`, `RG`, `Znum`,
`Mtot`, `sixq7`, `eclear`). It rejects eight mutations (root scale 1, root
scale 2 only inside the bracket, centre sign `+ Ω`, `θ = U b`, `S` with `Ybar`
for `Ybar + 1`, `Rc` sign `+ (b - c)`, `Sc` without `S²`, `2A - 1` for `2A`),
checks the literal and endpoint definitions verbatim and that `fixedPorts` is
textually the `IPRATrace75` one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers this circuit.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace111Estimate` | `omegaOf`, `omega_upper`, `omega_nonneg`, `three_lt_five` (ordered rings) |
| `Trace111Regs` | `omega`, `value111`, `value111_eq`, `value111_update`; `Trace111Omega.omega_data`, `omega_shift`, `omega_nonneg` |
| `Trace111Syntax` | `ev_regsW_Z`, literal `TenPositiveTrace111.expression`, `Trace111BFSSyntax.literal_zero_iff` |
| `Trace111ModelIff` | `positive_model_iff` |
| `IPRATrace111` | the iPRA endpoints |

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. The `_low2963` calibration, `product4` and package 194's natural and
integer equations are not covered. Package 194's quotient description (10)
of `Ω₂` and its sharper two-sided bound (11) are not formalized (only the
one-sided `Ω₂ ≤ 3 A U E |V|` and `Ω₂ ≥ 0` for `b ≥ 1`), nor is the early `p = 3`
projector (§3), which the `bV` weight does not need.
