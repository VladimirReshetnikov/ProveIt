# Fresh private witnesses and complete fourteen-to-thirteen arithmetic map

Date: 2026-10-25. Author: circuit_reduction. Independent whole source review
and fresh replay: ROOT.

| Source under `Lean/DiophantineConsistency/` | SHA-256 |
|---|---|
| ThirteenFreshSeed.lean | 6312b55f52b22306d2f070920bfc1b3002d397ae171b9dbcc9df828087781992 |
| ThirteenFreshSeedChecks.lean | 4f8cee845c533d4982dcd26af51172c6d631c1f4bf846c990897e4f55d259954 |
| ThirteenCarrierComplete.lean | 5f971560bae4ca88ba157fcb8a398e6f3f0bf418cd70491051c69bb8bf278fc0 |
| ThirteenCarrierCompleteChecks.lean | ef60e594e6b97dcd48e2a89c81d5da91440cfccf8de7dd9ef28102b866b9e107 |

ROOT read all217+34 and254+36 lines before independently executing the
respective modules/checks. Both modules and both focused checks exited0:

```sh
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/ThirteenFreshSeed.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenFreshSeed.lean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenFreshSeedChecks.lean
lake env lean -M6000 -j1 -o .lake/build/lib/lean/DiophantineConsistency/ThirteenCarrierComplete.olean Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCarrierComplete.lean
lake env lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ThirteenCarrierCompleteChecks.lean
```

All11 printed axiom reports contain only the standard `propext`,
`Classical.choice`, and `Quot.sound`, with the generic core identity needing
only `propext`. There are no admitted proofs or new axioms.

## Fresh seed audit

The rank and outer ordinate c=psi_A(R) are fixed before private witnesses
are chosen. A positive Pell ordinate divisible by b*c² supplies the new
strong seed. For R congruent3 modulo4, the auxiliary Qh polynomial gives
V+c divisible by f² and V+R divisible by c. Together with c dividing f²-1,
these construct a positive integer T in two exact quotient steps. There is
no assumed CRT solution or compatibility with a parent's private seed.

The negative signed ordinate satisfies y congruent1 modulo4*S² and the
literal auxiliary norm. Its bound y>-2V, together with positive divisible
transport G, constructs a positive independent m satisfying the complete
literal y expression. The checks include a nontrivial quotient, negative
y, the opposite rank1 sign, the failure of positive m at G=0, and the exact
scaled-strong factor.

## Complete map and its finite hypotheses

`ThirteenCarrierComplete` starts at an actual positive Carrier65 polynomial
zero. Its canonical31-source and the explicit finite mask interface derive
the exact outer Pell ordinate, rank positivity and w>q. Hence G>0, while the
actual W=1 equation proves b divides G. The additional finite residue
MC%4=2, the real two-bit low mask, and the four-block rank formula give
R%4=3. These facts are derived before selecting the fresh private seed.

The literal Fin14-to-Fin13 map preserves J,F,alpha,s,w,n,eta,zeta,gamma.
The complete core identity checks all retained and substituted fields;
its two fresh norms and two retained norms prove the actual69 polynomial
zero. The previously checked whole zero-set identities then give70 and71.
`polynomial_zero_completes` states these conclusions using the actual MVPs.

The extra low-mask residue is explicit. The focused finite control
ports[31,1,24,59], d5,MC24,MF28 satisfies both existing coefficient interfaces
while MC%4=0. That check asserts no polynomial solution and does not hide a
missing residue inside a supplied witness premise. The actual current mask
must discharge the extra residue when specializing this theorem.

The complete current kernel K, native tableau/computation equivalence and
internal-ZFC derivation are still required for a consistency endpoint.
These arithmetic maps supply no consistency decision or global minimum.
