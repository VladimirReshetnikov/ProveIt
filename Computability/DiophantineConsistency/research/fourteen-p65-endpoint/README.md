# Package 65's 14-positive degree-26 equation: iPRA endpoints

4 November 2026. Author-side build by the Claude session; not a paired replay.

## The equation

[`65-shared-taps/pell/circuits/p14_degree26.json`](../../con-zfc-diophantine-forms/65-shared-taps/pell/proof.md),
SHA-256 `0ceb30c9ba9b6a3387ac55d6591d56f5e9746626aaec6fecd2293402f233b137`:

- 14 strictly positive unknowns `j F α z f i T x Y r η ζ u γ`;
- 92 operations and exact degree 26;
- the whole compact44 tuple `β K0 MC MF`.

With `J = 3j + 1`, `q = 1 + βJ`, `C = q − F − α` and `X = q + x`, it is the
sum of five squared residuals:

- `A0`, the first carrier;
- `Nm`, the main carrier, with modulus `M = 4q²Y`;
- `At`, the transport;
- `Aa`, the auxiliary norm;
- `As`, the ordinary strong norm.

It is the point *26 / 92* of the fourteen-positive Pareto row of the
[collection README](../../con-zfc-diophantine-forms/README.md).

## What is proved in Lean

[`Compact44/IPRAPositive65`](../../Lean/DiophantineConsistency/Compact44/IPRAPositive65.lean)
states:

- `positiveBridge`: in every model of `𝗜𝚺₁`, the equation has a positive zero
  iff machine 215 halts;
- native, standard and equality-only iPRA proofs of
  *no zero of `positiveShift expression`* ↔ *Con(ZFC)*, for the selected
  Foundation ZFC consistency predicate.

**Reuse of package 72's P13 proof.** The equation is P13's predecessor, and
most of P13's soundness transfers. P13's main register is
`Dhat = β·Dstar`, with the same `M`, `S` and `γ`. So once the residuals are
read in a model, P13's generic sections apply unchanged:
`P72Window.window_ring`, `P72Early.early` and `P72Power.power`.

The one structural difference is the strong norm. P13 has the normalized
`f² = 1 + Δ(c²i)²`, while 65 has the ordinary `(ic²)² = Δ(f²−1)`.
`P72Exact` already passed through the ordinary index `i' = Δi` internally, so
it was split:

- `exact_ordinary` takes the ordinary index and norm directly;
- P13's `exact` is now its corollary at `i' = Δi`.

The modules:

1. **Graph** (`P65Graph`). The gates come from the JSON, checked by
   `tools/generate_p65.py --check`. The module proves the five-squares split
   of zeros and the ring evaluation of each residual.
2. **Residuals in a model** (`P65Root`). In every `𝗜𝚺₁` model:
   - the ordinary strong norm;
   - `q³ ∣ Y` and the first Pell norm, by integrality of the root of
     `(Y + q³(r+ℓ))² = q⁶(1 + ℓ(ℓ+k))`;
   - the gap `F + α < q` and the transport identity
     `qA = ((F+α)A + Fq) + (q−1)(qz)`, with `A = X + K0·q`;
   - the auxiliary norm;
   - the main root `g` with P13's carrier relation.
3. **Zero ⇒ six leaf facts ⇒ halting** (`P65Facts`). The leaf valuation is
   `![J, F, α, 1, 1, X, Y, 1, η, ζ, 1, 1]`, and
   `CompactLeafFactsHalt.halts_of_facts` closes it.
4. **Halt ⇒ zero** (`P65ConvZero`, `P65Converse`). P13's extraction of the
   canonical halt data is reused verbatim. The new witnesses:
   - `j > 0`: `N = 581197^(2T+4) ≥ 2` gives `q > 2^590069 = β + 1`, so
     `J > 1`;
   - `x = 2^R − q > 0`: `2^R = q·2^(R−u)` with `R > 2u`;
   - `i = Δ·i_norm`, the ordinary strong index;
   - `r = τ − (ℓ + s)`, where P13 had `+qz`, because `At` carries the
     transport separately;
   - `z` is the halt data's transport quotient, already positive.

## Checks

- **Graph binding:** `tools/generate_p65.py --check` passes: 92 gates.
- **Build:** each module was built serially (one `lake build` per call,
  `LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`), with no errors and no warnings. The
  refactored `P72Exact` and the P13 and P14 endpoints were rebuilt unchanged.
- **Axiom reports:** every report is within
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, `native_decide`,
  `axiom`, `unsafe` or `implemented_by` appear in the new modules.

## Scope and limits

- **Not an independent replay.**
- **External binding.** The JSON coefficient payloads are bound to the Lean
  ports by the same external binding as for the compact44 free-J literal.
  Exact degree 26 is the package's claim, not a Lean theorem.
- **The degree-30 / 85-operation companion** `p14_degree30.json` of the same
  package is not covered. It is not on the Pareto row: 64's 30 / 83 dominates
  it.
