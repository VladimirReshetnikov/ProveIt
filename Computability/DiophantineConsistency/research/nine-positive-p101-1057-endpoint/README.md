# Nine-positive point 101/1,057: iPRA endpoint

Target: package 101's `nine/equations/boundary_complete.json` (nine positive unknowns
`b g h s w C i j n`, 1,057 live operations, exact degree 997,810, SHA-256 `3f5f4f92…`) on the
tree-calibrated wang943-mixed-121x8801 tuple (`Mixed121Ports.ports`). The endpoint has the usual
shape (`positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence`), as
for the 101/420 point in `../nine-positive-p101-420-endpoint/`.

**Status: endpoint closed.** `IPRANine101p1057` proves `positiveBridge` and the native, standard and equality-only iPRA equivalences for the Lean literal of the 1,057 equation at the wang943-mixed-121x8801 ports, with only `[propext, Classical.choice, Quot.sound]`. The literal is bound to the pinned JSON by `tools/check_graph.py`.

## What the package certificate certifies

The complete-radical form differs from the 420 form only in its second radicand and majorant:
`σ = 1024C⁵i`, `a₁ = DFI·σ²`, `V₁ = Π(A, C, i, Z)` with the 333-term polynomial `Π` of
`data/saturated_corrected_P.json` (`Π = P₀ + 297874·C²⁴i⁶Z`, `data/correction.json`).
Nodes 0–434 of the JSON are byte-identical to `boundary_simple.json`; nodes 435–1367 evaluate `Π`
in Horner form, 1369 is `σ`, 1371 is `a₁`.

The 36,309-term certificate `data/saturated_corrected_certificate.json` certifies **the plain
identity** `Π² − σ²DFI`, not another normalization: in the variables `(A, C, i, Z)`,
`Π² − σ²DFI` has only **2,599 terms** (coefficients below 2⁵⁵, degrees `(18, 48, 12, 2)`), because
`Π` agrees with `σ√(DFI)` to all orders in `A` down to `A⁰` and the top half of `Π²` cancels
against `σ²DFI` (whose `A`-degree is 36). The certificate is exactly the translate of that
2,599-term defect by `A = x + 3, C = y + 1, i = u + 1, Z = v + 1` (36,309 positive coefficients;
checked exactly by the generator). The `A`-degree 18 of the certificate is the cancellation, not a
different normalization.

## Route

The prefix, layout and contract are 101's unchanged (`W = 115`, height 1866): `N101Prefix`,
`N101Contract`, `N101Layout`, `Source31*`. Only the finalizer, the majorant certificate, the graph
and the endpoint are new.

```
nine-variable zero (b g h s w C i j n > 0), N ≥ 32 (IPRANine101p1057.N32)
  ──[N1057Finalizer.sound: strict majorants (N1057Majorant.majorant), m > 0, roots, σ ∣ √a₁]──▶
      N² ∣ C(2R,R), b = 2ᵏ, g < 4t                                       (prefix R, N, t)
  ──[N101Contract.contract]──▶ gapN86 rows(z + 1) = 0 ──[source_of_code]──▶ parent zero
  ──[Source31Facts.halts]──▶ machine 215 halts
converse: halt ──[Source31Converse.converse, code_of_source, contract]──▶ N² ∣ C(2R,R)
  ──[N1057Finalizer.complete, Π > AD]──▶ nine-variable zero
```

### The majorant in Lean

`N1057Majorant.majorant`: for `a ≥ 2²⁰` and `c, i, z ≥ 1` in any ordered commutative ring,
`DFI·σ² < Π²` and `aD < Π`. (In the finalizer, `A ≥ 8N⁴ ≥ 2²⁰` because `N ≥ 32`.)

* `defect_eq : Π² − DFI·σ² = defect` (the 2,599-term defect as a literal term tree) in every
  commutative ring. Expanding `Π²` by sparse list arithmetic in the kernel is infeasible here
  (measured: about 30–47 KB of kernel memory per merge step; `Π²` needs about 870,000 steps). The
  identity is instead checked by **one Kronecker evaluation** (`Kron4`): the integer expression
  `Π² − DFIσ² − defect` is split into a difference `e⁺ − e⁻` of natural expressions; the kernel
  checks the syntactic degree box `37 × 49 × 13 × 3`, the coefficient sums `e^±(1,1,1,1) < 2⁷²`,
  and `e⁺ = e⁻` at `(X, X³⁷, X^{37·49}, X^{37·49·13})`, `X = 2⁷²` (numbers of about 5.09 Mbit,
  GMP arithmetic; the literal term tree is packed relative to each node's lowest index).
  `Kron4.kcheck_sound` proves that this implies the identity in every commutative semiring
  (through `MvPolynomial (Fin 4) ℕ`: coefficient `≤` value at ones, `degreeOf ≤ deg`, the
  Kronecker map to `ℕ[X]` is injective on the box, base-`X` digits).
* `def_check`: every monomial of the defect divides `a¹⁸c⁴⁸i¹²z²`, every negative coefficient sits
  at `a`-degree `≤ 17`, and `κ·2²⁰ + ν > 0` (`κ = 624687054848`, `ν` the sum of negative
  coefficients); `SP4.pos_of_check` then gives `defect > 0` for `a ≥ 2²⁰` (domination, not the
  package's translated certificate, which would need `a ≥ 3` only but 36,309 terms).
* `gapS_check`: the same domination check for `Π − aD` (336 terms, computed by `SP4` in the kernel).

## Modules (`Lean/DiophantineConsistency/Nine121/`)

| Module | Content | Build |
|---|---|---|
| `SparsePoly4` | handwritten: sparse 4-variable polynomials (fuelled merge, products), `ev_add/sub/mul/lit` for every list; `posCheck` and `pos_of_check` (domination positivity in ordered commutative rings) | built, clean (about 20 s) |
| `Kron4` | handwritten: natural/integer polynomial expressions `NE`/`ZE`, term trees, `split`, packed evaluation `pkT`, `kcheckK`, `kcheck_sound`, `zero_of_kcheckK`; tree form `posCheckT` of `posCheck` | built, clean (about 25 s, peak about 2.3 GB) |
| `N1057Majorant` | generated (`tools/generate_n1057_majorant.py`): `piBlock` (JSON nodes 435–1367 over arbitrary operations), `PiR`, `PiS`; `Dr Fr Gr Hr Ir sig`; the defect tree `defT`; `id_check`, `def_check`, `gapS_check` (`decide +kernel`); `defect_eq`; `majorant` | built, clean axioms (`majorant`; about 40 s, peak about 3.0 GB: the Kronecker check takes seconds) |
| `N1057Finalizer` | sibling of `N9Finalizer` (reuses `S.*`, `marg`, `Qr`, `a0`, `V0`, `N9Finalizer.a1`, `register_sizes`): `value`, `sg`, `a1`, `Zr`, `V1`; `A_big`; `value_eq`; `sound` and `complete` (hypothesis `N ≥ 32`) | built, clean axioms (`value_eq`, `sound`, `complete`; about 17 min, peak about 2.8 GB) |
| `N101p1057Graph` | generated (`tools/generate_n101p1057_graph.py`): one `def` per JSON node, gate-local lemmas; `r1367 : node 1367 = N1057Majorant.PiR A C i Z` (the block unfolded, literals as integer constants, `rfl`); `r1369 : σ`, `r1371 : a₁`; `output_eval : eval = N1057Finalizer.value (Rq) (Nq) b g (tq) h s w C i j n` | built, clean axioms (`output_eval`; about 4 min, peak about 3.6 GB) |
| `IPRANine101p1057` | `N32`, `expression` (node 1385 at the ports), `expression_def`, `forward`, `backward`, `positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` | built: all four endpoint theorems `[propext, Classical.choice, Quot.sound]` (about 6 min wall, 2 min compile, peak about 3.6 GB) |

Nothing in the committed 101/420 or 105/456 modules was changed.

## Checkers

* `tools/generate_n1057_majorant.py --check`, `tools/generate_n101p1057_graph.py --check`:
  byte-identical regeneration. The majorant generator first checks, with an exact Python model of
  the Lean algorithms, that the block is the 333-term `saturated_corrected_P.json`, that
  `Π² − σ²DFI` is the 2,599-term defect, that its translate is the 36,309-term certificate, both
  domination conditions, the Kronecker degree box and bounds, and `e⁺ = e⁻` at the Kronecker point.
* `tools/check_binding.py` → `CHECK.json`: the 101/420 bindings (generated layout byte-identical,
  parent rows, port SHA-256 = package 55's wang943-mixed-121x8801 payloads); nodes 0–434 and the
  prefix parameters of `boundary_complete.json` equal those of `boundary_simple.json`;
  `N1057Majorant.lean` byte-identical; five mutations rejected (majorant coefficient against the
  package `P` and against the Kronecker equality, defect coefficient, shared prefix node, port
  hash).
* `tools/check_graph.py` → `CHECK_GRAPH.json`: `N101p1057Graph.lean` byte-identical (numeric gate
  modulo 2¹²⁷ − 1 at random points, with `Π` evaluated independently from the 333-term JSON); every
  `def nᵢ` parsed back and compared gate by gate with the pinned JSON; the endpoint expression; the
  `piBlock` lets parsed back and compared with nodes 435–1367; ten mutations rejected.

## Axioms

Every built theorem prints `[propext, Classical.choice, Quot.sound]`: `N1057Majorant.majorant`, `N1057Finalizer.value_eq/sound/complete`, `N101p1057Graph.output_eval`, and `IPRANine101p1057.positiveBridge/native_equivalence/standard_equivalence/reference_equivalence`.

There is no `sorry`, `native_decide`, `axiom`, `unsafe`, `implemented_by` or `maxHeartbeats 0`.
The kernel checks are `decide +kernel`. Finite heartbeat raises are used (up to `8000000`).

## Scope and non-claims

* What is shown: in native, standard and equality-only iPRA, *no natural zero of
  `positiveShift IPRANine101p1057.expression`* ↔ *Con(ZFC)* for the selected Foundation ZFC
  consistency predicate. Here `expression` is the Lean literal `N101p1057Graph.n1385` at
  `Mixed121Ports.ports`.
* The correspondence of that literal with the JSON circuit (`check_graph.py`), and of the ports,
  the shared prefix and the majorant data with package 101's files (`check_binding.py`), is a
  finite external check, not a Lean theorem. This is not a paired replay.
* Lean does not use the package's 36,309-term translated certificate; it re-derives the 2,599-term
  defect identity (Kronecker check) and certifies positivity by domination for `A ≥ 2²⁰`, which the
  prefix guarantees. The equality of the translate with the package certificate is checked only by
  the generator.
* The exact degree 997,810 is a package claim; it is not re-proved here.

## What remains

Nothing for the 1,057 endpoint itself. `Kron4` is generic (any four-variable polynomial identity with a syntactic degree box); package 82's Laurent-cone point (`nine_full_radical`, 726 operations) is now closed with it on package 71's source65 prefix and Pell registers, see [`../nine-positive-p82-726-endpoint/`](../nine-positive-p82-726-endpoint/README.md).
