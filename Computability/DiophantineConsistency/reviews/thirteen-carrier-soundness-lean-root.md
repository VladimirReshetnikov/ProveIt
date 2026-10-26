# Whole positive thirteen-variable zero restoration

Date: 2026-10-25. Author: circuit_reduction. Independent reviewer and fresh
replay: ROOT. This review concerns the actual three thirteen-coordinate
polynomials, with all four fixed ports preserved.

## Reviewed and checked sources

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| ThirteenCarrierSoundness.lean | 50478151e2e94dcdf150838df7a60660ce93dfb57fb6bea03e0251e8801687ce |
| ThirteenCarrierSoundnessChecks.lean | 2dc648236c4917a6ab59a27708e0c6f222841da6077566cfac338b256fce620a |

ROOT read the complete 290-line module and 40-line focused checks before
freshly executing either. Both commands exited zero:

```sh
lake env lean -j1 -o .lake/build/lib/lean/DiophantineConsistency/ThirteenCarrierSoundness.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCarrierSoundness.lean
lake env lean -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCarrierSoundnessChecks.lean
```

The eight printed axiom reports contain only `propext`, `Classical.choice`
and `Quot.sound`, with the core identity requiring only the first and last.
There are no new axioms, admitted proofs or computational trust extensions.
The focused checks cover the exact coordinate order, the single b multiplier
on i, the recovered quotient for z, both actual norm factors, a negative
auxiliary pair, and a counterexample showing why m positivity is necessary.

## Mathematical audit

The complete generic core identity updates the parent's U,W,y fields and
leaves its other fields unchanged. It identifies the entire literal69 value
with delta times the product of four actual factors minus one. Positivity
and the existing exclusions of minus-one norms force all four factors to
one. No rank sign, C sign, G sign or signed-y sign is assumed.

The auxiliary norm gives y nonzero and abs(y)<2*abs(V). Together with the
literal y formula and positive b,m, that bound forces G>=0. The signed Pell
residue proves 4*S^2 divides y-1; cancelling4 and using b divides S derives
b divides G. Thus z=G/b+1 is a positive integer. Replacing the derived signed
y by abs(y), and replacing the old i by b*i, preserves the exact norms and
makes every one of the fourteen parent coordinates positive. W is exactly
one, not an assumed transport equation.

`polynomial_zero_restores` accepts a positive zero of any one of the actual
69,70,71 polynomials and returns the explicit positive assignment at which
the actual Carrier65 polynomial vanishes. It uses the previously checked
whole positive zero-set identities to cover70 and71. The endpoint is not a
claim only about a special subset of thirteen-variable zeros.

## Remaining boundary

This is the full forward arithmetic map. Fresh-seed completeness, production
of the required outer Pell/rank/transport data from the current native
encoding, the current tableau/computation equivalence and internal-ZFC
formalization remain separate requirements. No Con(ZFC) endpoint or global
minimality claim is made by this checkpoint. The whole umbrella and every
ancestor were not replayed; the new module and its checks were freshly run
against the recorded prerequisite objects.
