# Package 72 P13 (13 positive, degree 28, 98 operations): iPRA endpoint plan

Opened 4 November 2026. Claude session, at Vladimir's choice ("Package 72 P13
here"). The source is
[`72-congruence-sextic/positive13`](../../con-zfc-diophantine-forms/72-congruence-sextic/positive13/PROOF13.md),
with circuit `p13_degree28.json`, SHA-256
`1968b1a0c887eb5a94794d8fdd7635f56432da4d235e81cf5ce4ab4790840d49`, on the
whole compact44 tuple.

## Why no cheap reduction exists

- **The witness transform fails.** On a free-J zero,
  `r = τ − ell − k − s + t(k·qm + 1)`, where `τ ≈ ell + k/2` and
  `t = Bt/(q−1) = q(z_old − 1)`. So every free-J zero has `z_old ≥ 2`. P13
  deliberately allows `z_old = 1`. Some P13 zeros therefore have no free-J zero
  with the same transport data, and P13 must reach halting through the
  shared halting chain itself.
- **The two carriers are parametrized differently.**
  - first carrier: P13 has `Z = M0(ell + r) + (q−1)Y − q³Bt`, with no folded
    `k − k·Bt`;
  - main carrier: P13 has `Dhat = β·Dstar`, with `M = 4q²Y` and `S = 4qY`;
  - strong equation: P13 has the normalized `f² − ΔI² = 1`, with `I = c²i`,
    where free-J has the ordinary `I² = Δ(f² − 1)`;
  - `J` is recovered from `As = 0` by rational-root integrality.

## The shared halting chain: measured interface

`hzgraph.py` (this session's scratchpad) computes the call graph of literal-zero
hypotheses reachable from `FixedGraphMarkedHaltDraft.graph_halts`:

- 60 theorems;
- 54 only forward `hz`;
- 6 are mathematical leaves.

| Leaf | Conclusion | P13 source |
| --- | --- | --- |
| `FreeJExactOrdinary.exact_ordinary_indices` | first and main indices, `pi = R`, `2j = R+1`, Pell coordinates | §6, signed auxiliary index ⇒ `p = R` |
| `FreeJFirstTransport.freej_first_factor_transport` | `(F+α)A + Fq < qA`, `F+α < q` | `C ≥ 1` |
| `FreeJGraphCongruenceExplore.first_pair_mod` | `((F+α)A + Fq) % Jβ = qA % Jβ` | §5, `q−1 ∣ Bt` |
| `FreeJPowerFinish.graph_power` | `X = 2^R` | Pell growth plus main projection, with `gcd(q,H) = 1` |
| `FreeJPowerProjection.graph_projection` | `q ∣ 3X`, `q ≤ 3X` | §6, `q ∣ X` |
| `FreeJRootBinding.first_scaled_norm` | `|Z|² = M²(1 + ell(ell+k))` on the free-J `Z` syntax | replace it by its consumers' conclusions (`q³ ∣ Y`, the first-root quotient) |

The non-leaf `first_quotient` (`k = R+1+4XY²t`) and `growth` (`2^R < Y`)
are also needed by `graph_power`.

## Phases

1. **Interface.** Define `Compact44Facts p v`, the conjunction of the leaf
   conclusions, minus `first_scaled_norm` (its consumers' conclusions
   replace it). Retype `hz` in the 54 forwarding theorems, and turn leaf calls
   into field projections. Prove `facts_of_literal` from the existing leaves.
   Rebuild the chain and every dependent endpoint (95-op through 87/51).
   - This pays off beyond P13: every compact44 equation that proves `Facts`
     gets halting.
   - It changes promoted modules beyond their imports, so it needs a new
     review record.
2. **P13 soundness.** P13 zero ⇒ `Compact44Facts` at the pseudo-valuation
   `![J, F, α, f−1, T, X, Y, r', η, ζ, n, γ']`. The chain's `hv` is used only at
   the indices the leaves need, which must be checked. The steps:
   1. §4: `As = 0` ⇒ `b ∣ Nf` ⇒ `J = 3j+1`; integral `R`; packing bounds.
   2. §5: `M0 ∣ Z` ⇒ `q³ ∣ Y`, `q−1 ∣ Bt`, the first norm with `|τ|`.
   3. §6: main root `g`; `gcd(S,H) ≤ 3`; Pell classification; strong rank
      `c ∣ m`; the signed auxiliary index (package 61 `SIGNED_INDEX_LEMMA`) ⇒
      `p = R`; `2n = R+1`; `q ∣ X`.
   4. growth `2^R < Y`, projection ⇒ `X = 2^R`.
   5. §7: transport facts.
3. **P13 converse.** Halt ⇒ P13 zero, from the canonical halt data
   (`FreeJHaltModelZero`: `J = rep N` with `N` odd ⇒ `J ≡ 1 (mod 3)`). Take
   `f0 = f − j`, `T` and `u` from the squared-modulus reconstruction, and
   `r = τ − ell − s + t`, `γ = γ_old + v/M − w`.
4. **Endpoint.** The `IPRAOrdinary12Chain` helpers, the record, the docs.

Proposed size: Phase 1 is about 60 module edits, mechanical and verified by
rebuild. Phases 2–3 are about 15–25 new modules.
