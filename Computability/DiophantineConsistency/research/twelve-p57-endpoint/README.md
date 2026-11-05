# Package 57's 12-positive degree-258 equation: iPRA endpoints

4 November 2026. Author-side build by the Claude session; not a paired replay.

## The equation

[`57-separated-degrees/low_degree/twelve_positive_degree258.json`](../../con-zfc-diophantine-forms/57-separated-degrees/low_degree/PROOF.md),
SHA-256 `9e9db19a68ddb52e0b2c75accb68b7d082a78d338fe03239f2ce73dcf7829188`:

- 12 strictly positive unknowns `J F α z i T s w η ζ y t`;
- 89 operations and exact degree 258;
- the whole compact44 tuple.

With `q = βJ + 1`, `X = wq`, `Y = sq³`, `U = 4q⁴` and `S = UH`, the equation is
`Nt·(1 + N)·(1 + J_M) − 1 = 0`. Its factors are:

- `Nt`, the transport;
- `N = (W² + U²G − S²A)² − 4W²·U²G`, with
  `W = U(X + ac) + H(U(t + ℓ) + (k − R − 1))`. It fuses the main and first
  carriers;
- `J_M = Z² − 4Dv²b²`, with `I = ic²`, `Q = (ΔI)²`, `D = ΔI·I + 1`, `v = cT`,
  `b = c + RD` and `Z = (Dv² + b² − 1) + (Q − 1)y(2 − Qy)`. It fuses the
  normalized strong norm and the auxiliary norm.

It is the twelve-positive Pareto point *258 / 89* of the
[collection README](../../con-zfc-diophantine-forms/README.md).

## What is proved in Lean

[`Compact44/IPRAPositive57`](../../Lean/DiophantineConsistency/Compact44/IPRAPositive57.lean)
states:

- `positiveBridge`: in every model of `𝗜𝚺₁`, the equation has a positive zero
  iff machine 215 halts;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*.

### New mathematics

1. **The product-unit guard** (`P57Units`). Every factor is `±1`. Both `N`
   and `J_M` have the shape `P² − 4w`, so a value `−2` would give
   `P² + 2 = 4w`, which is impossible modulo 4.
2. **The four-root restoration of the fused carrier** (`P57Root.four_root`).
   - `N = 0` makes `(W² + U²G − S²A)/(2WU)` a rational, hence integral, square
     root `g` of `G`.
   - Then `(W − Ug)² = S²A` gives `τ` with `τ² = A`, and `W = Ug ± Sτ`.
3. **The strong and auxiliary restoration** (`P57Root.strong_aux`).
   - `J_M = 0` gives `f` with `f² = D`, from `Z/(2vb)`.
   - It also gives the auxiliary norm `Q·V² + y₀² = 1 + Q·y₀²`, with
     `y₀ = Qy − 1`.
   - The sign of `f` is not fixed, so the ordinate `V = fv − b` is either the
     ordinary-blank ordinate `|cTf − (f²R + c)|` or its *plus* form
     `cTf + (f²R + c)`.
   - `OrdinaryBlankSignedIndex.signed_half_index_blank_plus` is new. It handles
     the second sign: its residues modulo `f` and `c` are again `±c` and `±R`.
4. **The early congruence from the fused carrier** (`P57Early.early_of_mod`).
   - In either sign, `W ≡ H(k − R − 1) (mod U)` and `U ∣ S`. Together these
     give `(H·k) % U = (H(R+1)) % U`.
   - `P62Early.gcd_dvd_three` removes `H`.
   - Unlike packages 62 and 72, the first carrier is not a separate factor.
     So the first index comes from `τ² = A` alone.

### Assembly and converse

- **`P57Facts`** combines these pieces with `P72Window.window_ring`,
  `P72Exact.index_window` and `index_close`, and `P72Power.power_of_mod`. It
  yields the six compact44 leaf facts.
  - The power step uses `g ≡ X + ac (mod H)`. This follows from either carrier
    sign once `2n = R + 1` gives `U ∣ k − R − 1`.
- **`P57ConvZero` and `P57Converse`** build the converse from the canonical
  halt data. The witnesses are:
  - `z + 1`, the halt data's `i`, and `f·T`;
  - `sY` and `w = 2^(R−u)`;
  - `y = (y_halt + 1)/(Δic²)²`, which is integral by
    `ArithmeticOddOrdinateResidue.pair`, because the constructed rank is
    `≡ 3 (mod 4)`;
  - `t = γold + τ − ℓ − sY·q·t4`, which is positive because `τ² = ℓ(ℓ + k) + 1` and `4·sY·q·t4 ≤ k` give `τ > ℓ + sY·q·t4`.
- The inner-norm identity holds only after multiplication by `Q`. The converse
  therefore cancels `Q ≠ 0` in the model's ring of differences before calling
  the ring-generic `P57ConvZero.output_zero`.

## Checks

- **Graph binding:** `tools/generate_p57.py --check` passes: 89 gates.
- **Build:** each module was built serially (one `lake build` per call,
  `LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`), with no errors and no warnings.
- **Axiom reports:** every report is within
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  `axiom`, `unsafe` or `implemented_by` appear in the new modules.

## Scope and limits

- **Not an independent replay.**
- **External binding.** The JSON coefficient payloads are bound to the Lean
  ports by the same external binding as for the compact44 free-J literal.
  Exact degree 258 is the package's claim, not a Lean theorem.
- **No coefficient-binding file.** Package 57 ships no
  `coefficients/COEFFICIENT_BINDING.json`. Its proof states the
  package-39/44 tuple with `B = 2^590069`, which is the tuple the Lean ports
  use.
