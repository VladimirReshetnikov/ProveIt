# Package 72's P13 and P14: iPRA endpoints

4 November 2026. Author-side build by the Claude session; not a paired replay.
The campaign log is in [PLAN.md](PLAN.md).

## The equation

[`72-congruence-sextic/positive13/p13_degree28.json`](../../con-zfc-diophantine-forms/72-congruence-sextic/positive13/PROOF13.md),
SHA-256 `1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49`:

- 13 strictly positive unknowns: `F α C f0 i T X Y r η ζ u γ`;
- 98 operations and exact degree 28;
- the whole compact44 tuple, with six derived fixed leaves: `β+1`, `3β`,
  `(3β)²`, `L = β(3β)²`, `b²L²` and `4β`.

It is the thirteen-positive frontier point *28 / 98* of the
[collection README](../../con-zfc-diophantine-forms/README.md), the lowest
degree at thirteen positive unknowns.

## What is proved in Lean

[`Compact44/IPRAOrdinary72`](../../Lean/DiophantineConsistency/Compact44/IPRAOrdinary72.lean)
states:

- `positiveBridge`: in every model of `𝗜𝚺₁`, P13 has a positive zero iff
  machine 215 halts;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*, for the selected
  Foundation ZFC consistency predicate.

**The proof does not reduce to an existing literal.** Every zero of the free-J
graph forces transport quotient `z_old ≥ 2`, while P13 deliberately allows
`z_old = 1`. So there is no witness transform, and the build goes through
three layers.

1. **The compact44 halting chain, re-based on six facts** (`3eb716174d`).
   - `CompactLeafFacts.LeafFacts` bundles the six facts:
     - the exact Pell indices;
     - the gap `q > F + α`;
     - the first-pair congruence;
     - `X = 2^R`;
     - `q ∣ 3X`;
     - `q³ ∣ Y`.
   - The 49 forwarders of the chain are restated over it in `Compact44/Facts/`.
     These are generated companions; no promoted module changed.
   - `CompactLeafFactsHalt.halts_of_facts` then gives halting from the facts.
   - Any compact44 equation that supplies the six facts gets halting.
2. **P13 zero ⇒ the six facts** (`P72Root`, `P72Main`, `P72Aux`, `P72Mu`,
   `P72Window`, `P72Early`, `P72Exact`, `P72Power`, `P72Facts`). This follows
   PROOF13 §4–§6:
   - rational-root integrality gives `q = 1 + β(3j+1)`;
   - the first root gives `q³ ∣ Y` and the transport congruence;
   - the main root `g` comes from `A1`;
   - the gcd cancellation, with `gcd(4qY, H) ∣ 3`, gives `2n ≡ R+1 (mod μ)`
     with `R + 1 < μ`;
   - the signed half-index theorem gives `m = R`; then `2n = R+1` and
     `q ∣ X`;
   - the main projection and Pell growth give `X = 2^R`.
3. **Halt ⇒ P13 zero** (`P72ConvArith`, `P72ConvZero`, `P72Converse`). This
   uses the canonical halt data of `CompactHaltFirstGamma`:
   - `J = rep N ≡ 1 (mod 3)`, because `N = 581197^(2T+4)` is odd and
     `q = 2^(590069N) ≡ 2`;
   - the witnesses `f0 = f − j`, `r = τ + qz − (ell + s)`, `u = y − w` and
     `γ = γ_old + t/4 − X/q` are each shown positive;
   - all four residuals vanish identically (`P72ConvZero.residuals_zero`).

## Checks

- **Graph binding:** `tools/generate_p72.py --check` passes: 98 gates and 6
  derived leaves.
- **Build:** every module was built serially (one `lake build` per call,
  `LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`), with no errors and no warnings.
  `P72Graph` and `P72Converse` disable only the unused-simp-argument linter.
- **Axiom reports:** every report is within
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  `axiom`, `unsafe` or `implemented_by`.

## Scope and limits

- **Not an independent replay.** This is my own build.
- **External binding.** The binding of the JSON coefficient payloads to the
  Lean ports is the same external binding as for the compact44 free-J
  literal. Exact degree 28 is the package's claim, not a Lean theorem.
- **Build traps met along the way:**
  - instantiating the concrete ports, or unfolding `rankExpr` at the concrete
    ports, crashed `lean.exe` silently (stack overflow, exit `0xC0000409`). The
    fix was generic `B K L H` statements and a ring-generic `rankExpr_eval`;
  - `betaNat` must be locally irreducible wherever `simp` might see it.

## The fourteen-positive sibling P14

[`72-congruence-sextic/positive14/p14_degree24.json`](../../con-zfc-diophantine-forms/72-congruence-sextic/positive14/PROOF14.md),
SHA-256 `91a307011482e1850b97ae4a4222f024bcbbde00a7a7850e6635e8b875729495`,
is the fourteen-positive frontier point *24 / 101*:

- 14 strictly positive unknowns: P13's thirteen and `E`;
- 101 operations and exact degree 24.

Its gates are P13's, except in three places:

- P13's register `E := X * Y` becomes the input `E`, and the product is
  recomputed as `Eprod`;
- there is one extra residual `AE = E − Eprod`;
- the output is P13's `A0² + A1² + Aa² + As²` plus `AE²`.

[`Compact44/IPRAOrdinary72P14`](../../Lean/DiophantineConsistency/Compact44/IPRAOrdinary72P14.lean)
proves:

- `P72P14.zero_iff`: in every model of `𝗜𝚺₁`, a P14 zero is exactly a P13 zero
  of the first thirteen coordinates with `E = XY`. Once `E = XY`, the four P13
  residuals evaluate as P13's (`residuals_eval`), and a sum of five squares
  vanishes only when each square does;
- `positiveBridge`: P14 has a positive zero iff P13 has one. This composes
  with P13's `positiveBridge`: the converse sets `E := XY`, which is positive
  because `X` and `Y` are;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*.

**Checks.**

- `tools/generate_p14.py --check` passes: 101 gates and 6 derived leaves.
- The module was built serially, with no errors or warnings.
- Every axiom report is within `[propext, Classical.choice, Quot.sound]`.
