# Package 64's 14-positive degree-30 equation: iPRA endpoints

4 November 2026. The original build was author-side. A later [independent captured-provider replay](../fourteen-p64-independent-replay/README.md) rebuilt the eight modules with one import shim and passed an [artifact review](../../reviews/p64-captured-replay-independent/README.md); this is not a paired or full-transitive source replay. The package’s missing pinned files were subsequently [restored and externally verified](../fourteen-p64-payload-provenance/RESTORATION.md).

## The equation

[`64-structural-reductions/positive14/polynomial.json`](../../con-zfc-diophantine-forms/64-structural-reductions/positive14/PROOF.md),
SHA-256 `b9731360a30bcbcfd6f9161241cafb01b8c5d68aa40b84ddc50ba689a0745d0e`:

- 14 strictly positive unknowns `J F α z f i T Y w ρ η ζ e γ`;
- 83 operations and exact degree 30;
- the whole compact44 tuple `β K0 MC MF`.

With `q = βJ + 1`, `X = wq`, `U = Y²` and `C = q − F − α`, it is
`A0² + M² + W² + Na² + Lt² − 1`. The residuals are:

- `A0`, the first carrier;
- `M`, the main carrier with modulus `U = Y²`;
- `W`, the ordinary strong norm;
- `Na`, the auxiliary norm;
- `Lt`, the transport.

It is the point *30 / 83* of the fourteen-positive Pareto row of the
[collection README](../../con-zfc-diophantine-forms/README.md).

## What is proved in Lean

[`Compact44/IPRAPositive64`](../../Lean/DiophantineConsistency/Compact44/IPRAPositive64.lean)
states:

- `positiveBridge`: in every model of `𝗜𝚺₁`, the equation has a positive zero
  iff machine 215 halts;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*, for the selected
  Foundation ZFC consistency predicate.

### What is new relative to packages 72 and 65

1. **The local norm minimum** (`P64Norm`). A zero makes the five squares sum
   to one. Write `Na = A(x² − y²) + y²`, with `A = Δ(f²−1)`, `x = |V|` and
   `y = |V + e|`.
   - **`Na = 0` is impossible.** If `f = 1`, then `A = 0` and
     `W = (ic²)² ≥ 81`, which is too large. Otherwise `A ≥ 2`, and `Na = 0`
     would make `A(A−1)` a square, by integral square roots
     (`na_ne_zero`). But `A(A−1)` lies strictly between `(A−1)²` and `A²`.
   - **`Na = −1` is impossible modulo four** (`na_ne_neg`, by `decide` over
     `ZMod 4`).
   - **The rest follows by discreteness:** `Na = 1` and the other four
     residuals vanish (`sq_split`).
   - `V` enters only through some representation `ι P − ι N`, so this
     step needs no rank bound.
2. **The early congruence for `U = Y²`** (`P64Early`).
   - `H = 4(X+1)Y + 3` gives `H² + 16(X+1)²Y² = 9 + 8(X+1)Y·H`. So
     `gcd(U, H) ∣ 9`, and `U ≤ 9μ`.
   - Then `9(R+1) < 9q⁴ ≤ q⁶ ≤ U ≤ 9μ`, which forces `(2n) % μ = R + 1`.
   - No coprimality of `q` and `H`, and no residue of `q`, is used.
3. **Carrier-free generic cores.**
   - `P72Exact.indices_ordinary` gives `13 ≤ n < m = R` and `2n = R+1`
     without any carrier.
   - `P72Power.power_of_mod` gives `X = 2^R` from `g ≡ X + ac (mod H)`.
   - P13's `exact` and `power` are now wrappers around them.
   - For 64, `q ∣ X` is immediate from `X = wq`. Cancelling `U` in the
     carrier, once `2n = R+1`, gives `g ≡ X + ac (mod H)`.
4. **The converse** (`P64ConvZero`, `P64Converse`). It reuses P13's
   extraction of the canonical halt data. The new witnesses:
   - **`z` and `w`:** the halt data's transport `(K + w)C = F + z(q−1)` is
     exactly `Lt = 0`, with `w = 2^(R−u)`;
   - **`γ = γold + 4X·s'`:** since `k = R + 1 + 4XY²s'`, the main shift
     `Uγ − (k − R − 1)` equals `U·γold`. So `γ` needs no subtraction;
   - **the remaining witnesses:** `J > 0` from `q ≥ 2`, the ordinary strong
     index `Δi`, and `ρ = τ − (ℓ + s)`.

The modules are `P64Graph`, `P64Root`, `P64Norm`, `P64Early`, `P64Facts`,
`P64ConvZero`, `P64Converse` and `IPRAPositive64`.

## Checks

- **Graph binding:** `tools/generate_p64.py --check` passes: 83 gates.
- **Build:** each module was built serially (one `lake build` per call,
  `LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`), with no errors and no warnings.
  The refactored `P72Exact` and `P72Power` keep every earlier statement.
- **Axiom reports:** every report is within
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  `axiom`, `unsafe` or `implemented_by` appear in the new modules.

## Scope and limits

- **Not an independent replay.**
- **External binding.** The JSON coefficient payloads are bound to the Lean
  ports by the same external binding as for the compact44 free-J literal.
  Exact degree 30 is the package's claim, not a Lean theorem.
