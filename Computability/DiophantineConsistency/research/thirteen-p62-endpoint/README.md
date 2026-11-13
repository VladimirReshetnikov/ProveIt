# Package 62's 13-positive degree-114 equation: iPRA endpoints

4 November 2026. Author-side build by the Claude session; not a paired replay.

## The equation

[`62-sign-and-norm/positive13/polynomial.json`](../../con-zfc-diophantine-forms/62-sign-and-norm/positive13/PROOF.md),
SHA-256 `37c2382bbcdf137eee9714c6d59ead0c9215c71ff6bd0edb502191d16542a85b`:

- 13 strictly positive unknowns `J F α z f i T s w η ζ γ t`;
- 83 operations and exact degree 114;
- the whole compact44 tuple.

The equation is `Nt·(1 + Nmain)·Ns·(1 + N) − 1 = 0`. Its factors are:

- `Nt`, the transport;
- `Nmain`, the main carrier, with modulus `U = 4q⁴`;
- `Ns`, the strong norm;
- `N`, a centered two-root norm. It fuses the first Pell norm and the
  auxiliary norm of the ordinary-blank ordinate `V = c(Tf − 1) − Rf²`.

It is the thirteen-positive Pareto point *114 / 83* of the
[collection README](../../con-zfc-diophantine-forms/README.md).

## What is proved in Lean

[`Compact44/IPRAPositive62`](../../Lean/DiophantineConsistency/Compact44/IPRAPositive62.lean)
states:

- `positiveBridge`: in every model of `𝗜𝚺₁`, the equation has a positive zero
  iff machine 215 halts;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*.

### New mathematics

1. **The ordinary-blank signed index theorem**
   (`OrdinaryBlankSignedIndex.signed_half_index_blank`). The tree's signed
   half-index theorem was stated for the squared-modulus ordinate
   `f²(Tc − R) − c`. Its core `ArithmeticPellHalfIndex.half_index` only uses
   `|V|` modulo `f` and modulo `c`. For `V = c(Tf − 1) − Rf²` these
   residues are `±c` and `±R`, the second because `f² ≡ 1 (mod c)`. So the
   rank is again the Pell index. Package 57 uses the same ordinate.
2. **The product-unit guard** (`P62Units`). Each factor is `±1`. The three
   negative cases fail modulo 4:
   - `D*² + 2 = (4q⁴)²G`;
   - `I² + 2 = Δ(f²−1)`, where `Δ(f²−1)` is `0` or `1` modulo 4;
   - `core² + 2 = 4dAE`.
3. **The centered two-root restoration** (`P62Root.two_root`).
   - `N = (d(x²+A) − E)² − 4d²x²A` makes `(d(x²+A) − E)/(2dx)` a rational,
     hence integral, square root `±τ` of `A`.
   - Then `E = d(x ∓ τ)²`, which is the auxiliary norm with `y = |x ∓ τ|`.
   - `|V| ≥ 1`, because `V = 0` would give `core² = −4dA`.
4. **The early congruence modulo `4q⁴`** (`P62Early`). Here `J` is free, so
   `3 ∣ q` is possible, and `gcd(4q⁴, H) ∣ 3` needs a real argument
   (`gcd_dvd_three`):
   - `36 + 4H·q³m = 12H + 4q⁴·q²m²` gives `g0 ∣ 36`;
   - `H` is odd, so `g0 ∣ 9`;
   - `g0` is then a numeral `≤ 9`, and `g0 = 9` fails both ways: if
     `3 ∤ q` then `4q⁴ ≡ 1 (mod 3)`, and if `q = 3t` then
     `H ≡ 3 (mod 9)`.
   - A bound of only `g0 ∣ 9` would not suffice: `4q⁴/9 < R + 1` is possible.
5. **Reusable index steps** (`P72Exact.index_window`, `index_close`). These
   are P13's index argument with its signed step removed, so either signed
   theorem can be inserted between them.

### Assembly and converse

- **`P62Facts`** combines the above with `P72Window.window_ring` and
  `P72Power.power_of_mod` into the six compact44 leaf facts.
  - `q ∣ X` holds outright, from `X = wq`.
  - The transport gives `(K0 + w)C = F + (z−1)·βJ`.
- **`P62ConvZero` and `P62Converse`** build the converse from the halt data.
  The witnesses are:
  - `z + 1`, `Δ·i`, `f·T`, `sY`, `w = 2^(R−u)`;
  - `γold + sY·q·t4`;
  - `t = τ − ℓ + y`.

## Checks

- **Graph binding:** `tools/generate_p62.py --check` passes: 83 gates.
- **Build:** each module was built serially (one `lake build` per call,
  `LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`), with no errors and no warnings.
- **Axiom reports:** every report is within
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  `axiom`, `unsafe` or `implemented_by` appear in the new modules.

## Scope and limits

- **Not an independent replay.**
- **External binding.** The JSON coefficient payloads are bound to the Lean
  ports by the same external binding as for the compact44 free-J literal.
  Exact degree 114 is the package's claim, not a Lean theorem.
