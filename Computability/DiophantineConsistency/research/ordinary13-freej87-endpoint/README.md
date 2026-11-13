# 13-positive, 87-operation free-J equation: iPRA endpoints

3 November 2026. Author-side build by the Claude session; not a paired replay.

## The equation

Package 115's [`positive13_87_degree51.json`](../../con-zfc-diophantine-forms/115-synchronized-exponents/supplement/circuits/positive13_87_degree51.json),
SHA-256 `24b9120cc07693ba3fab0bff254c071fae800d14415850c3411651c026e28f0c`
(as in the package's `SHA256SUMS` and `supplement/MANIFEST.json`):

- 13 strictly positive unknowns: `J F alpha f i T X Y r eta zeta u gamma`;
- 87 binary operations;
- exact degree 51;
- the four compact44 ports `β = 2^590069 − 1`, `K0`, `MC` and the
  already-shifted `MF`.

It shares `coefficients/BINDING.json` with `positive12_95_degree70.json`,
the 95-operation free-J literal whose all-model calibration is in the tree.
It is the thirteen-positive frontier point *51 / 87* of the
[collection README](../../con-zfc-diophantine-forms/README.md).

## What is proved in Lean

| Module | Content |
| --- | --- |
| [`Compact44/FreeJ13`](../../Lean/DiophantineConsistency/Compact44/FreeJ13.lean) | the 87-gate graph; ZMod 4 exclusion of the negative unit for each of its four factors; ring evaluation at the embedded 12-variable valuation; the two tail identities |
| [`Compact44/FreeJ13Halt`](../../Lean/DiophantineConsistency/Compact44/FreeJ13Halt.lean) | in every model of `𝗜𝚺₁`, a positive zero of the 87-gate graph exists iff a positive zero of the 95-operation literal exists, hence iff machine 215 halts |
| [`Compact44/IPRAOrdinary13`](../../Lean/DiophantineConsistency/Compact44/IPRAOrdinary13.lean) | native, standard and equality-only iPRA: *no zero of `positiveShift expression`* ↔ *Con(ZFC)*, for the selected Foundation ZFC consistency predicate |

**Gates 1–64.** These coincide with the 95-operation literal's carrier prefix,
so `A0` and `A1` evaluate to that literal's first and main residuals. The tail
has two factors:

- `Fs = 1 + ((c²i)² − Q)`;
- `Fa = y² − Q(y² − V²)`, with `y = V + u`.

**13 → 12** (`forward`, for arbitrary integer ports):

1. The four factors multiply to one. Each is excluded from `−1` modulo 4, so
   each is `+1`.
2. The 12-variable witness takes `t = f − 1` and `n = i + u`.
3. `t > 0`, because `t = 0` gives `Q = 0`, which would force `c²i = 0`.
4. Once `Q = c⁴i²`, the auxiliary equation makes the ordinary residual `N`
   vanish identically (`tail_forward`, a single `linear_combination`).

**12 → 13** (`backward_ports`):

- `graph_positive_auxiliary` supplies `i`, `Z` and `y` with `(icc)² = Q` and
  `Q·Z² = (Q−1)·y² + 1`, where `Z` is the value of `V`.
- Since `Z > c ≥ 1` and `Q ≥ 1`, the second equation forces `y > Z`.
- So `u = y − Z` is positive.

The masks enter only through `L = lowNat` and `H = highNat`, as in
`symbolic_aligned`.

## Binding and checks

- `generate_graph.py` emits the Lean gate block from the pinned JSON.
  `generate_graph.py --check <FreeJ13.lean>` passes: all 87 gates match.
- **Build:** three targets, one `lake build` per call, with `LAKE_JOBS=1` and
  `LEAN_NUM_THREADS=0`. Every target exited 0, with no warnings.
- **Axiom reports:** every report in the three modules is within
  `[propext, Classical.choice, Quot.sound]`. The three endpoints and
  `positive_model_iff` report exactly that set.
- **Source scan:** no `sorry`, `native_decide`, `axiom`, `unsafe` or
  `implemented_by`.

## Scope

- **Not an independent replay.** This is my own build.
- **External binding.** The binding of the JSON coefficient payloads to
  `CompactSymbolicModelIff.p` is the same external binding as for the
  95-operation literal. Exact degree 51 is the package's checked claim, not a
  Lean theorem.
- **Build note.** A first version of `backward` instantiated the concrete
  ports before the proof. The compiler then exited silently after 324 s.
  Restating the proof over symbolic `B K L H` fixed it.
