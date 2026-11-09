# Nine-positive point 101/420: internal route toward the iPRA endpoint

Target: package 101's `nine/equations/boundary_simple.json` (nine positive
unknowns `b g h s w C i j n`, 420 live operations, exact degree 1,472,168) on
the tree-calibrated wang943-mixed-121x8801 tuple. The aim is the usual endpoint
shape (`positiveBridge`, `native_equivalence`, `standard_equivalence`,
`reference_equivalence`), as for `Mixed121/IPRAPositive55`.

**Status: a fully proved prefix, not yet the endpoint.** The 31-input source
is now calibrated to machine 215 in every model of `𝗜𝚺₁`, in both directions.
Most of the internal arithmetic the nine-variable reduction needs is also
proved. The digit-extraction contract assembly, the literal 420 graph and the
endpoint are still missing. The open part is listed at the end.

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
| `N101Layout` | translated weights and targets, the 6+36+39 kernel records, the 74+37+6 target interactions, `coeff_target : [T^{q_k}](K₂U²+K₁U+K₀) = 2ρ_k` | generated and checked by `check_binding.py`; **Lean build not completed.** The first attempt died silently after 70 min under heavy paging. A retry passed 9.9 GB private memory within 6 min and was stopped. The monolithic `decide +kernel` certificate `hS2` (22·37,479 triples over `Fin 31 × Fin 31 × Fin 39`) is the likely cause. Planned fix: split it per target and first coordinate (22·31 small decides), and prove `coeff_target` row by row |
| `SparseCentral` | `noCarry_iff_sq_dvd_sparse`: for `R = L(S+T+1) − S − 1`, `L = 2ᵘ`, `2ν = u + σ(T)`, `NoCarry S T ↔ (2^ν)² ∣ C(2R,R)` | built, clean axioms |
| `SignedDigits` | borrow propagation of signed radix digits; `target_digit`; `high_noCarry_iff` (the high-block carry test) | built, clean axioms |
| `DigitPopulation` | populations of radix-`2^v` digit sums, `σ(2^v − 2^k) = v − k` | built, clean axioms |
| `LowMask` | `noCarry_code_iff_weights`: no carry against the low code mask iff `g = Σ zᵢ B^{wᵢ}` with `zᵢ < b` (weight 0 allowed) | built, clean axioms |
| `SatPell` | saturated positive ProductPell certificate: `psi_of_sat` (soundness) and `exists_sat` (completeness) | built, clean axioms |
| `N9Norm` | `norm2`, its four-factor form, positivity outside the majorants, internal root extraction | built, clean axioms |
| `N9Finalizer` | the literal saturated simple finalizer `value`; `value_eq`; `sound` (a positive zero gives `N² ∣ C(2R,R)`, `b = 2ᵏ`, `g < 4t`); `complete` (from `N² ∣ C(2R,R)`, `b = 2ᵏ`, `g < t`, a positive zero) | built, clean axioms |

Generated files: `tools/generate_n101_layout.py` (use `--check` to verify).
`N101Layout.lean` is deliberately **not committed** until it builds within
this machine's memory. Run the generator to recreate it; `check_binding.py`
needs it on disk.
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

Finding: package 101's kernels share one position between several rows. For
example, position 1056 serves `fo`, `iC2` and `sN`. So the
one-record-per-position framework `DegreeSeparatedCoding` does not apply.
`SparseExtraction` replaces it.

## Axioms

Every built theorem prints `[propext, Classical.choice, Quot.sound]`. There is
no `sorry`, `native_decide`, `axiom` or `maxHeartbeats 0`. Finite heartbeat
raises are used: up to `8000000` in generated and finalizer modules.

## Scope and non-claims

* No endpoint theorem for the 420 equation exists yet, so no iPRA claim is made
  for it.
* `Source31Facts`/`Source31Converse` concern the package-31 parent source
  (`parent_quartic31`) at the 121x8801 ports. They are tuple-level and reusable
  for every equation coded from that source: 101's 420 and 1,057, 105's 456,
  and 106's 10ℤ forms.
* The finalizer module is the literal saturated simple finalizer of 101/105.
  The complete-radical (1,057) and Laurent (82's 726) majorants are not covered.

## What remains for the 420 endpoint

1. **Contract assembly** (`N101Contract`), for `b = 2ᵏ`, `B = 2^{κ+2k}`, `κ = 2134939`:
   * low mask: `ModelDigitTransfer.noCarry_code_iff` at the 31 weights, then
     the digit sum written as `Σ zᵢ B^{wᵢ}`;
   * high block: `SignedDigits.high_noCarry_iff` at height 1867. This needs
     `G* = eval B (sourcePoly ports (z+1))` as a range sum, and the coefficient
     bound `4|c_e| + 4 ≤ B` from `SparseExtraction.abs_coeff_*_le`. That in turn
     needs port bounds in the model (`K < 2^1070004` is not yet proved
     internally) and `|c_p| ≤ 2^2134927` for each of the 81 kernel coefficients;
   * `ModelCarries.noCarry_concat` at `N₀ = B^116`, and the bound `S + T < L`;
   * calibration: `SparseCentral` with `σ(T) = 138v − 31k − 22`, from
     `DigitPopulation`;
   * unconditional positivity of `G*`, so that `R` is a model natural before the
     finalizer recovers `b = 2ᵏ`.
2. **Prefix evaluation**: the graph's `R, N, t` are `ι` of model naturals, with
   `R, N ≥ 8` and `b ≤ R, N`.
3. **`N101p420Graph`**: the Lean literal of the 451-node DAG, with fixed leaves
   as port polynomials and the base and threshold scales `2^2134939` and
   `2^16012032` kept irreducible. Its register-by-register evaluation to
   `N9Finalizer.value`, and a gate-by-gate JSON checker.
4. **`IPRANine101p420`**: `positiveBridge` from the chain above, then
   `IPRAOrdinary12Chain.native_of_positive/standard_of_positive/reference_of_positive`.
