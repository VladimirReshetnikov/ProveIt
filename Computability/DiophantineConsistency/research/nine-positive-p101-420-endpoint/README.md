# Nine-positive point 101/420: iPRA endpoint

Target: package 101's `nine/equations/boundary_simple.json` (nine positive
unknowns `b g h s w C i j n`, 420 live operations, exact degree 1,472,168) on
the tree-calibrated wang943-mixed-121x8801 tuple. The aim is the usual endpoint
shape (`positiveBridge`, `native_equivalence`, `standard_equivalence`,
`reference_equivalence`), as for `Mixed121/IPRAPositive55`.

**Status: endpoint closed.** `IPRANine101p420` proves `positiveBridge` and the native, standard and equality-only iPRA equivalences for the Lean literal of the 420 equation at the wang943-mixed-121x8801 ports, with only `[propext, Classical.choice, Quot.sound]`. The literal is bound to the pinned JSON by `tools/check_graph.py`.

## Route

```
nine-variable zero (b g h s w C i j n > 0)
  ──[N9Finalizer.sound]──▶ N² ∣ C(2R,R), b = 2ᵏ, g < 4t          (prefix R, N, t)
  ──[contract: SparseCentral + SignedDigits + low mask]──▶
      g = Σ zᵢ B^{wᵢ}, zᵢ < b, gapN86 rows(z + 1) = 0             (N101Layout.coeff_target)
  ──[N101Source.zero_iff, affine map]──▶ positive parent zero
  ──[Source31Facts.halts]──▶ machine 215 halts (Mixed121Halt.halts_of_facts)
converse:
  halt ──[Source31Converse.converse]──▶ parent zero ──▶ gapN86 zero ──▶ code g, b = 2ᵏ large
       ──[contract]──▶ N² ∣ C(2R,R) ──[N9Finalizer.complete]──▶ nine-variable zero
```

## Modules (`Lean/DiophantineConsistency/Nine121/`)

| Module | Content | Status |
|---|---|---|
| `Source31Rows` | literal parent rows (verbatim copy of `SplitCertificate59.sourceRows`) and their ring consequences `facts` | built |
| `Source31Facts` | `facts_ports`: a positive parent zero in any `𝗜𝚺₁` model gives `CompactLeafFacts.LeafFacts` at `![J,F,α,1,1,X,Y,1,η,ζ,1,1]` for any ports with the four leaf bounds; `halts`: at `Mixed121Ports.ports`, an internal halt of machine 215 | built, clean axioms |
| `Source31Converse` | `rows_zero` (ring level) and `converse`: from `Mixed121Seeds.halt_first_gamma`, an explicit positive parent zero | built, clean axioms |
| `N101Source` | gapN86 rows (generated) and their identity with the parent under `P_old = P + η + ζ`, `N_old = N + 1` and the row operations `ρ₁₃ = r₁₃ + r₁`, `ρ₁₄ = r₁₄ + r₂` | built |
| `SparseExtraction` | word and kernel polynomials, coefficient extraction over explicit index finsets, coefficient bounds `H(Σu)²`, `HΣu`, `H` | built |
| `SparseCheck` | kernel-cheap completeness certificates for sparse extraction: a structural pair loop over the weight list with one bit test of a position mask per pair (`chkI`, `chkJ`, `chk1`), turned into the exact index characterisations by `quad_iff`/`lin_iff` (the kernel position is recovered by injectivity); `coeff_sum_monomial_list` | built |
| `N101Layout` | translated weights and targets, the 6+36+39 kernel records, the 74+37+6 target interactions as index lists, `coeff_target : [T^{q_k}](K₂U²+K₁U+K₀) = 2ρ_k` | built, clean axioms (about 4 min; peak about 3 GB). The first version decided the index sets by brute force over all 22·37,479 triples and exceeded 9.9 GB. Now 22 pair checks of 961 pairs each certify them through `SparseCheck` |
| `SparseCentral` | `noCarry_iff_sq_dvd_sparse`: for `R = L(S+T+1) − S − 1`, `L = 2ᵘ`, `2ν = u + σ(T)`, `NoCarry S T ↔ (2^ν)² ∣ C(2R,R)` | built, clean axioms |
| `SignedDigits` | borrow propagation of signed radix digits; `target_digit`; `high_noCarry_iff` (the high-block carry test) | built, clean axioms |
| `DigitPopulation` | populations of radix-`2^v` digit sums, `σ(2^v − 2^k) = v − k` | built, clean axioms |
| `LowMask` | `noCarry_code_iff_weights`: no carry against the low code mask iff `g = Σ zᵢ B^{wᵢ}` with `zᵢ < b` (weight 0 allowed) | built, clean axioms |
| `SatPell` | saturated positive ProductPell certificate: `psi_of_sat` (soundness) and `exists_sat` (completeness) | built, clean axioms |
| `N9Norm` | `norm2`, its four-factor form, positivity outside the majorants, internal root extraction | built, clean axioms |
| `N9Finalizer` | the literal saturated simple finalizer `value`; `value_eq`; `sound` (a positive zero gives `N² ∣ C(2R,R)`, `b = 2ᵏ`, `g < 4t`); `complete` (from `N² ∣ C(2R,R)`, `b = 2ᵏ`, `g < t`, a positive zero) | built, clean axioms |
| `N101Prefix` | the prefix of `report_section.tex` (eq. origin-prefix) in any commutative ring (`Bq`, `ell`, `Tst`, `ker0/1/2`, `Ust`, `Gs`, `N0`, `maskq`, `Tcq`, `Scq`, `Lq`, `Rq`, `Nq`, `tq`; scales `baseScale = 2^2134939`, `thresholdScale = 2^16012032` irreducible); `Gs_sum` (range-sum form, `natDegree ≤ 1866`); in an ordered ring with `|c_p| ≤ H`, `4096Hb² ≤ B`: `Gs_pos` (unconditional `G* > 0`), `Gs_le`, `coeff_bound` (`4|c|+4 ≤ B`), `sum_lt_L` (`S*+T_c < L`, `g < N₀`, `M₀ < N₀`) | built |
| `N101Contract` | at `Mixed121Ports.ports`: `port_facts` (all 81 kernel coefficients `≤ 2^2134927` from `β < 2^1064921`, `K < 2^1070004`, `MC < β`, `MF < 2β`); `prefix_naturals` (`R, N, t` model naturals, `R, N ≥ 8`, `b ≤ R, N`, `t > 0`); `high_iff`; `pop_low`/`pop_high` (`σ(T_c) = 138v − 31k − 22`); `contract`: for `b = 2ᵏ`, `g < 4t`, `N² ∣ C(2R,R) ↔ ∃ z < b, g = Σ zᵢB^{wᵢ} ∧ ρ(z+1) = 0`; `source_of_code`, `code_of_source` (positive `g < bB¹¹⁵` via the all-ones row 4) | built, clean axioms |
| `N101p420Graph` | generated (`tools/generate_n101p420_graph.py`): one `def` per JSON node, gate-local evaluation lemmas (closed forms in `Bq b`, prefix registers, 24 finalizer registers over register atoms), `value_regs`, `output_eval : eval = N9Finalizer.value (Rq) (Nq) b g (tq) h s w C i j n` | built, clean axioms (`output_eval`; about 17 min under memory pressure, peak about 3.5 GB) |
| `IPRANine101p420` | `expression` (node 451 at the ports), `expression_def`, `forward`, `backward`, `positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` | built: `positiveBridge`, `native_equivalence`, `standard_equivalence`, `reference_equivalence` all `[propext, Classical.choice, Quot.sound]` |

Generated files: `tools/generate_n101_layout.py` and `tools/generate_n101p420_graph.py` (use `--check` to verify).
`N101Layout.lean` is generated; `--check` and `check_binding.py` compare it byte for byte.
Binding checker: `tools/check_binding.py`, output in `CHECK.json`. It checks the
following:

* the generated Lean files are byte-identical to a fresh generation, which
  re-derives every gapN86 row from the parent through the affine map and the
  row operations, and re-derives the 22 extraction identities from
  `kernels.json`;
* `Source31Rows.rows` parses to the 22 equations of `parent_source.json`
  (SHA-256 `1c336ba0…`);
* 101's four original31 port SHA-256 values equal package 55's
  wang943-mixed-121x8801 payloads (the tuple of `Mixed121Ports.ports`);
* five mutations are rejected: a kernel coefficient, a weight, a target, a
  parent-row coefficient and a port hash.

Graph checker: `tools/check_graph.py`, output in `CHECK_GRAPH.json`. It regenerates `N101p420Graph.lean` byte for byte (the generator first checks every closed form, every register formula and output = value(prefix) on the JSON DAG modulo 2^127 − 1 at random points), parses every `def nᵢ` back and compares it gate by gate with the pinned JSON (SHA-256 `ea0804c3…`), checks the endpoint expression, and rejects seven mutations (child, operation, literal, variable, coefficient recipe, scale, and a JSON literal that must change the output).

Finding: package 101's kernels share one position between several rows. For
example, position 1056 serves `fo`, `iC2` and `sN`. So the
one-record-per-position framework `DegreeSeparatedCoding` does not apply.
`SparseExtraction` replaces it.

## Axioms

Every built theorem prints `[propext, Classical.choice, Quot.sound]`. There is
no `sorry`, `native_decide`, `axiom` or `maxHeartbeats 0`. Finite heartbeat
raises are used: up to `8000000` in generated and finalizer modules.

## Scope and non-claims

* What is shown: in native, standard and equality-only iPRA, *no natural zero
  of `positiveShift IPRANine101p420.expression`* ↔ *Con(ZFC)* for the selected
  Foundation ZFC consistency predicate. Here `expression` is the Lean literal
  `N101p420Graph.n451` at `Mixed121Ports.ports`.
* The correspondence of that literal with the JSON circuit (`check_graph.py`)
  and of the ports with package 101's original31 payloads (`check_binding.py`)
  is a finite external check, not a Lean theorem. This is not an independent
  paired replay.

* `Source31Facts`/`Source31Converse` concern the package-31 parent source
  (`parent_quartic31`) at the 121x8801 ports. They are tuple-level and reusable
  for every equation coded from that source: 101's 420 and 1,057, 105's 456,
  and 106's 10ℤ forms.
* The finalizer module is the literal saturated simple finalizer of 101/105.
  The complete-radical (1,057) and Laurent (82's 726) majorants are not covered.

## What remains

Nothing for the 420 endpoint itself. The prefix, layout and contract here are
reused by 105's 456 form ([`../nine-positive-p105-456-endpoint/`](../nine-positive-p105-456-endpoint/README.md))
and by 101's complete-radical 1,057 form
([`../nine-positive-p101-1057-endpoint/`](../nine-positive-p101-1057-endpoint/README.md)),
both now closed. A shorter evaluation proof of the graph would only matter if
build time does.
