# Package 73's 13-positive degree-30 equation: iPRA endpoints

4 November 2026. Author-side build by the Claude session; not a paired replay.

## The equation

[`73-guard-reanchoring/positive/p13_degree30.json`](../../con-zfc-diophantine-forms/73-guard-reanchoring/positive/PROOF.md),
SHA-256 `e96cd6c8950711a6a26392b27c1ab531cb9df37277e0426cc40cdd1138846a5b`:

- 13 strictly positive unknowns `j F α f i T X Y r η ζ u γ`;
- 92 operations and exact degree 30;
- the whole compact44 tuple.

It is the thirteen-positive Pareto point *30 / 92* of the
[collection README](../../con-zfc-diophantine-forms/README.md). Package 74
evaluates the same polynomial in 93 operations. The endpoint below is about
the polynomial, so it covers 74's evaluator once that circuit is checked to
compute it. That check has not been done here.

## What is proved in Lean

[`Compact44/IPRAPositive73`](../../Lean/DiophantineConsistency/Compact44/IPRAPositive73.lean)
states:

- `positiveBridge`: in every model of `𝗜𝚺₁`, the equation has a positive zero
  iff machine 215 halts;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*.

**The forward direction is a reduction to the 95-operation free-J literal**
(`P73Graph`, `P73Halt`). With `J = 3j + 1`:

- 73's first carrier is the literal's. Expanding `W = 1 + k(q−1)` turns
  `M(ℓ+k+r) + Y(q−1) − Bt·W·q³` into the literal's folded
  `M(ℓ+k+r − k·Bt) + Y(q−1) − q³·Bt`.
- Its main carrier is gate for gate the literal's, with modulus `U = q²Y`.
- The normalized strong norm `f² − 1 = Δ(c²i)²` is the ordinary norm with
  index `Δi`, because `Δ(f²−1) = c⁴(Δi)²`. So at
  `x = ![3j+1, F, α, f−1, T, X, Y, r, η, ζ, Δi + u, γ]` the literal's polar
  residual vanishes by `FreeJ13.tail_forward`.
- `f − 1 > 0`, because `f = 1` would force `Δ(c²i)² = 0`.
- The literal's halting calibration
  (`CompactSymbolicModelUnconditionalIff.model_iff`) then applies.

No new soundness mathematics is needed.

**The converse comes from the halt data** (`P73ConvZero`, `P73Converse`).
P13's extraction of `CompactHaltFirstGamma.halt_first_gamma` is reused.

- The witnesses `F α f i T X Y η ζ u` are the canonical ones. `i` is already
  the normalized strong index.
- `j > 0`, from `N ≥ 581197`.
- `r = τ + qz·W − (ℓ + k + s)`, which unfolds the literal's transport.
- `γ = γold + t − wX`: with `k = R + 1 + q²Y·t` and `XYq = q²Y·wX`, the main
  shift `Uγ + qXY − (k − R − 1)` is `U·γold`.
- No reverse map from literal zeros is needed. That map would have to
  produce a normalized strong index from an ordinary one, which a literal
  zero does not supply.

## Checks

- **Graph binding:** `tools/generate_p73.py --check` passes: 92 gates.
- **Build:** each module was built serially (one `lake build` per call,
  `LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`), with no errors and no warnings.
- **Axiom reports:** every report is within
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  `axiom`, `unsafe` or `implemented_by` appear in the new modules.
- **Build trap.** A first version of `first_lift` compared the two graphs'
  first residuals by unfolding both and calling `ring` on the expanded
  squares. It ran out of memory after 570 s. Comparing the carrier registers
  (`lit_first`, then `Z = root0` by a one-term `linear_combination`) is
  immediate.

## Scope and limits

- **Not an independent replay.**
- **External binding.** The binding of the JSON coefficient payloads to the
  Lean ports is the same as for the compact44 free-J literal. Exact degree 30
  is the package's claim, not a Lean theorem.
