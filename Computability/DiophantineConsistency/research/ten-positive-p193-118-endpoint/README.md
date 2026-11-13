# iPRA endpoints for package 193's ten-positive 118/190 `whole190` circuit

Package 193 (`con-zfc-diophantine-forms/193-transport-and-pell-reuse`) supplies,
in `positive/`, the principal circuit `whole190.json` (118 operations, exact
degree 190, root scale 4) and the companion `quotient202.json` (99/202, not
covered here; it is dominated). The ordinary proof is `positive/PROOF.md`
§§1–6. The circuit keeps package 172's 87/214 free-inverse chart (record
`research/ten-positive-p172-87-endpoint`; the Lean register `Y = q s` is
package 193's `Ybar`, `Am1 = A - 1`, `X Y² k = ell`, `v = X Y²`) and

* replaces the 87 transport gate `n - b V B` by `n - OmegaFold`, where package
  178's whole-product centre
  `Ω = U [2 S Rc + A (4 E V - θ Sc)]`, `θ = U² b`,
  `S = (k Ybar) [ell + k - (k Ybar) (Ybar + 1)]`, `e₂ = (k Ybar)²`,
  `Rc = θ (3 E + e₂) - (b - c)`, `Sc = 4 E² + 3 S² + e₂²`,
  is folded with the new transport weight `L = A U³ b²` into
  `OmegaFold = U [2 S Rc + A (4 E V - θ (Sc - b B))] = Ω + L B`
  (JSON rows `new_*`, `center`); the 87 rows `L = cTR V`, `LBt` are gone;
* replaces `G` by `16 G` in the norm (rows `new_scaledG`, `RG`):
  `P = Q (Z² - 16 M² G V²) + (16 M² G - Z²)`.

The `coefficient_binding` equals the 75/402 graph's exactly: the direct-BFS943
tuple, K0 raw `0a86821a…`, MC `6007cabd…`, MF `48333b0d…`, β `0664a868…`.

The Lean endpoints are in `Lean/DiophantineConsistency/BFS943/IPRATrace118.lean`
(namespace `DiophantineConsistency.IPRATrace118`): `positiveBridge`,
`native_equivalence`, `standard_equivalence`, `reference_equivalence`,
`standard_translated_equivalence`, `reference_translated_equivalence`, at the
same ports `fixedPorts` as `IPRATrace75`, with `expression_def :
expression = TenPositiveTrace118.expression (fun j => (fixedPorts j : ℤ))`.
Each depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Route

The circuit is neither an `n`-shift nor a rescaling of an already proved form:
its weight is `A U³ b²` instead of `b V`, and its roots are `z = ±4 g y`. The
route removes the root scale, proves `B ≥ 0` with the new weight directly,
and then hands the zero to the shifted 87 chain of
`research/ten-positive-p179-89-endpoint` (`Trace87Shift*`, which needs only
the 87 norm at a carrier `Z₈₇ - M ws` for an *arbitrary* `ws` together with
`B ≥ 0`, and ends in `BFS943FixedSource.FixedSource` and
`FixedSourceHalt.source_halts`). No new Pell, rank, projection or source layer
is needed.

**Folding** (`Trace118Regs`). `omegaFold_eq : OmegaFold = Ω + L B` (ring
identity), so the carrier is both `Z₈₇ - M (OmegaFold - b V B)`
(`regs118_Z_shift`) and `h D [H (n - L B) + K] - H [D B + h eclear] - M Ω`
(`regs118_Z_split`). The sign bounds below concern `Ω` and `L` only, as in
package 193 §1.

**Root scale four** (`Trace118Sign.shift_zero`, package 193 §2).
`norm16 r (4 Z') = 16 normValue r Z'`. `Q = 4 Δ a F0`, so `Q - 1` is odd and
`(Q - 1) Zc² = 16 (…)`; `Scaled87Sign.even_of_sq` applied twice gives
`Zc = 4 Zh` with `Zh` a zero of the unscaled 87 norm (the parity argument of
package 194 iterates). `Trace87NormRoots.graph_adjacent` gives `Zh = M z`,
`z = ±τ f y`, `g = τ f`, and the adjacent Pell norm at `|V|`.

**The centre** (`Trace118Estimate`, `Trace118Omega`). The Lean proof does not
use package 193's polynomial quotients `Q_j`; it bounds the literal evaluator
directly, which suffices because only crude bounds are consumed. At positive
inputs `S = k² Ybar ((X - 2) Ybar² + Ybar (Ybar - 1) + 1)` and
`0 ≤ S ≤ E`, `0 ≤ e₂ ≤ E` (`omega_data`). In the scalar form
(`x = A ≥ 2`, `0 < c ≤ U`):

* `omega_upper`: `Ω ≤ 5 A U E |V|` for every integer `b` (cases `b ≥ 1`:
  `8 U² E b + 2 c ≤ A V`; `b = 0`: `Ω = 2 U c (S - 2 A E) ≤ 0`; `b ≤ -1`:
  `8 A U³ E² |b| + 2 U E (|b| + c) ≤ 9 A U E |V|`);
* `omega_nonneg`: `Ω ≥ 0` once `b ≥ 1` (`8 A U² E b + 2 b ≤ 4 A V`).

**The weighted transport** (package 193 §4). `E ≤ U²`: the first-index size
`8 v + 4 ≤ k` (`Trace87NormKpos.graph_rank_size`, generic in the carrier) and
`c = k s + η ≥ k + 1` give `E = 1 + v (v + 1) k² ≤ (k + 1)⁴ ≤ c⁴ ≤ U²`
(`Trace118SizeCore.E_le`); `Δ = A (A + 2) ≥ 48` from `q ≥ 2`. Then
`Trace118Estimate.size_bound` gives `52 E F² + U² c < 2 U² (Q - 1)`
(`F = 1 + 2a`), and `weighted_estimate` derives from the adjacent norm alone
`b ≠ 0`, `y < 2 |V|`, `F |b| > 2 (Q - 1) - c`, hence `U² |b| > 52 E F` and,
with `g ≤ A U E` (`g_le`),

  `2 (4 g y + Ω) < 26 A U E |V| < 52 A U E F |b| ≤ A U³ b² = L`.

The weight-`L` carrier equals `M (4 z + Ω)`; with `2 eclear < L D`
(`eclear ≤ 6 N`, `N < b`; `L ≥ b` when `b ≥ 1`, `L > 0` always),
`TenPositiveCarrierTransport.model_nonnegative_of_carrier` gives `B ≥ 0` at the
positive `n` of the zero. Then `Z₈₇ - M ((OmegaFold - b V B) + 3 z) = M z = Zh`,
i.e. `Trace87ShiftTransport.ShiftZero p v (OmegaFold - b V B + 3 z)`. This uses
neither an auxiliary-index-five exclusion nor package 193's sharper
`|b| > 3 Δ f`, `|Ω - 4 A U E V| < A U E |V|`.

**Completeness** (`Trace118Complete.zero118`, package 193 §6, read at an
arbitrary positive 87 zero instead of the canonical witnesses). A halting time
gives a positive 87 zero (`Trace87HaltGraph.halt_zero_of_model_ports`) with
`Z₈₇ = M z`, `z = ±g y`, `B ≥ 0`, the mask, `R = rank ≤ c`
(`Trace87NormRank.graph_rank_exact`), `V > 0` (`Centred87Complete.V_positive`),
hence `b ≥ 1`, `Ω ≥ 0`, `L ≥ 0`. Since `L - b V` has no sign here, no
natural-shift lemma applies; instead put `n' = n + (OmegaFold - b V B) + 3 g y`
(if `z = g y`) or `+ 5 g y` (if `z = -g y`). The carrier at `n'` is `±4 Z₈₇(n)`,
so the norm is `16 value87 = 0`, and in cleared form
`M n' = 4 M g y + M OmegaFold - h D K + H D B + H h eclear > 0`, because
`OmegaFold = Ω + L B ≥ 0`, `y ≥ 1` and `K < 2 g`, `-eclear < 2 g`
(`Trace118Estimate.complete_bounds`, from `8 v + 4 ≤ k`, `k + 1 ≤ c`,
`R ≤ c` and `c² E ≤ g`). This is package 193's `|ρ| + κ + σ < g` in the weak
form `κ - ρ + σ < 2 g`.

`Trace118ModelIff.positive_model_iff` joins both directions; the iPRA wrappers
are those of `IPRATrace75`.

## Binding check

`check_lean_graph.py` (run `py -I -X utf8 -B check_lean_graph.py`) pins the
190 JSON (`28a66316…`), package 172's 87 JSON (also checking the JSON's
`parent.sha256`), the 75 JSON (port binding), the 87 record's checker (whose
parser and normalizer it imports) and the Lean sources that checker reads
(`TenPositiveTrace75.lean`, `Trace79Regs.lean`, `Trace82Regs.lean`,
`Trace87Regs.lean`). It checks the graph metadata (`whole190`, 118 operations,
degree 190, `transport_weight: A*U^3*b^2 (folded into Sc)`, `root_scale: 4`,
`6*q^7`) and that the JSON rows differ from the 87 rows exactly by the 35
centre/fold/`16 G` gates and the four removed 87 weight rows; transcribes
`value87` with the 87 checker (re-checked against the 87 JSON), then parses
`omegaFold` (with its lets `kY`, `S`, `e2`, `theta`, `Rc`, `Sc`), `regs118` and
`value118` into the same interned DAG and compares with the JSON output after
exact commutative-ring structural normalization (also the rows `new_kZ`,
`new_S`, `new_e2`, `new_theta`, `new_Rc`, `new_Sc`, `new_bB`, `new_ScShift`,
`new_Vdiff`, `new_Apart`, `new_SRc`, `new_Omega`, `center`, `new_scaledG`, `RG`,
`Znum`, `Mtot`, `sixq7`, `eclear`). It rejects eleven mutations (root scale 2,
root scale 4 only inside the bracket, fold sign `Sc + b B`, unfolded centre
`Sc`, `θ = U b`, `S` with `Ybar` for `Ybar + 1`, `e₂ = k Ybar`, `Rc` sign
`+ (b - c)`, `Sc` without `3 S²`, `A` read as `A - 1`, carrier `n + OmegaFold`),
checks the literal and endpoint definitions verbatim and that `fixedPorts` is
textually the `IPRATrace75` one, so
`reviews/bfs943-source-promotion/tools/check_ports.py` covers this circuit.
Output: `check-output.json`. These are finite external checks, not Lean
theorems about files.

## New modules (all in `Lean/DiophantineConsistency/BFS943/`)

| Module | Content |
|---|---|
| `Trace118Estimate` | `omegaOf`, `omega_upper`, `omega_nonneg`, `g_le`, `weighted_estimate`, `size_bound`, `complete_bounds` (ordered rings) |
| `Trace118Regs` | `omegaFold`, `regs118`, `norm16`, `value118`, `omega`, `weight`; `omegaFold_eq`, `norm16_four`, `regs118_Z_shift`, `regs118_Z_split`, `value118_update`; `Trace118Omega.omega_data`, `omega_nonneg` |
| `Trace118Sign` | `Trace118SizeCore.E_le`; `shift_zero` (positive 118 zero ⇒ `ShiftZero`) |
| `Trace118Complete` | `zero118` (positive 87 zero ⇒ positive 118 zero) |
| `Trace118Syntax` | literal `TenPositiveTrace118.expression`, `Trace118BFSSyntax.literal_zero_iff` |
| `Trace118ModelIff` | `positive_model_iff` |
| `IPRATrace118` | the iPRA endpoints |

## Scope and non-claims

The endpoints are about the Lean literal at the symbolic direct-BFS943 ports;
the JSON correspondence and the port hashes are the finite external checks
above. `quotient202.json`, package 193's exact-degree-190 certificate (§7) and
its quotient description of `Ω` (§3) are not formalized; only the one-sided
bounds `Ω ≤ 5 A U E |V|` (every sign of `b`) and `Ω ≥ 0` (`b ≥ 1`) are.
