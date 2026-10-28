# The internal polynomial bridge: module plan

> **Status 2026-10-28: complete.** Soundness (S1–S14):
> `ArithmeticSoundness2011.zero_halts`. Construction (K1–K7):
> `ArithmeticCurrentConstruction2011.halt_positive_zero`, with
> `ArithmeticLocalNormalization.localNormalization` (Matrix-free `MF*` port).
> Unconditional endpoint: `HACurrentEquation2011.ha_current_iff_consistency`.
> Module names below are the planned ones; several stages were split into
> helper modules (`ArithmeticCell*`, `ArithmeticConstruction*`,
> `ArithmeticController*`, `ArithmeticTiling*`, `ArithmeticPacking*`).

27 October 2026. Plan for the one premise still open in
`Lean/DiophantineConsistency/HACurrentAssembly2011.lean`:

```
PolynomialBridge : ∀ V ⊨ IΣ₂,
  classicalSentence holds in V  ↔  ¬∃ t, first (ArithmeticMachineRun215.run t) = 0
```

i.e. in every model, a positive zero of the literal 14-variable polynomial
exists iff the represented decimal215 run halts. With it,
`ha_current_iff_consistency_of_polynomial` is an unconditional HA derivation
of `unsolvabilitySentence ↔ ¬(ZFC proves ⊥)`; the source bridge is already a
theorem (`HACurrentAssembly2011.sourceBridge`, via
`ZFCinPA.ValidatorConsistency222`).

The two external directions are specified in detail (constants, file:line
references, finite-versus-global classification) in the read-only extractions
[soundness spec](ha-polynomial-soundness-spec-20261027.md) and
[construction spec](ha-polynomial-construction-spec-20261027.md); the tables
below summarize them.

## Transfer principle for finite facts

Every per-cell, per-tile and per-table fact concerns values below standard
bounds (bits, carries ≤ 57, digits < 2^47, tiles < 942, colours < 512,
states < 216). In any model of PA⁻ such values are numerals. A fact is
therefore transported by: (1) writing the internal hypothesis with `+ · / %`,
`fbit` and finite (standard-length) sums over `V`; (2) obtaining naturals `g`
with the data equal to `Nat.cast ∘ g`; (3) pushing the casts through (`Nat.cast`
is a semiring hom; `/`, `%`, `fbit` need cast lemmas); (4) invoking the existing
ℕ lemma. Fixed tables are nested-`if` numeral lookups (the
`ArithmeticMachineGraph215` pattern) checked by `decide`/structural lemmas in ℕ.
Only the global arguments (iterations over the nonstandard cell count, carry
chains, populations of big numbers, row induction) are re-proved internally.

## Soundness: positive zero ⇒ halt

| # | Module (planned) | Content | Spec |
|---|---|---|---|
| S1 | `ArithmeticBinaryCarry` (drafted) | `pop(a+1) ≤ pop a+1`; subadditivity; equality ⟺ NoCarry | A7 tools |
| S2 | `ArithmeticRepunit` (drafted) | `rep d N`, `(2^d−1)rep+1 = 2^{dN}`, `pop(a·rep) = N·pop a` | A2, A5 |
| S3 | `ArithmeticMaskConstants` | populations/parities of the standard masks by transfer | A5 |
| S4 | `ArithmeticHalfBinomial` + parts | represented power, Pascal binomials, Legendre `v₂(n!) = n − σ(n)`, Pell sandwich ⇒ `σ(R) ≥ 3u+2` | A6 (shared with K6) |
| S5 | `ArithmeticSaturation` | four-block rank + saturation ⇒ both ANDs vanish | A4, A7 |
| S6 | `ArithmeticWindowBits` | Boolean `c` from `C`; high-mask digits of `F` | A8, A9 |
| S7 | `ArithmeticCyclicWord` | represented word sums mod `ρ^n−1`; rotation; kernel congruence | A10 |
| S8 | `ArithmeticWindowCarry` | explicit end-around carries ≤ 57, digits, `word(d) = F` | A11 |
| S9 | `ArithmeticCellTransfer` | the cast-transfer framework for per-cell lemmas | §0 |
| S10 | `ArithmeticCellDecoding` | count ≤ 1, phase 0, labels, Start, copies | B0–B5, B7 |
| S11 | `ArithmeticWholeField` | `t ≡ 0 (mod 2011)` (offset-19 orbit via `θ^N = id`) | B6 |
| S12 | `ArithmeticOccupation` | every cell occupied; Δ0 tile assignment; MarkedWord | B8–B10 |
| S13 | `ArithmeticWangTable` | 942-tile table facts by transfer | C0 |
| S14 | `ArithmeticWangSoundness` | plane, initial strip (Δ0 LNP), walls, row step, row induction ⇒ halt before N | C1–C6 |

## Construction: halt ⇒ positive zero

| # | Module (planned) | Content | Spec |
|---|---|---|---|
| K1 | `ArithmeticRunTrace` | head position recursion, trace bounds up to T | M |
| K2 | `ArithmeticTilingWord` | closed-formula marked word on `N = p^{m+1}` cells | W |
| K3 | `ArithmeticPacking` | cell words with zero carries; scalars C, F, α, z, J; masks | P |
| K4 | `ArithmeticRankForcing` | `σ₂R = 3u+2`, `R ≡ 3 (mod 4)`, `R > 2u` | R |
| K5 | `ArithmeticController` | LTE, discrete-log surjectivity mod `d·p^{m+1}` (Hensel), dummy bits | K |
| K6 | `ArithmeticOuterSeed` | outer Pell seed (Kummer direction, binomial floor, sandwich) | S |
| K7 | `ArithmeticCurrentConstruction2011` | the 14 coordinates; factor identities | X, assembly |

Construction simplifications adopted from the extraction: drop unique Start;
constructed words have zero carry into and out of every cell (no cyclic carry
machinery); direct calibration identity `R(S) = R(∅) − Γ·P(S)`; Hensel
induction instead of pigeonhole; dimensions `ω = T+1`, height exponent `T+3`.

## Final step

`PolynomialBridge` from S14 (zero ⇒ halt) and K7 (halt ⇒ zero), each in every
model of IΣ1, plus the evaluation of `classicalSentence` in `V`.
