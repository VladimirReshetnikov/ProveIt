# Proof-status ledger

All numbered theorems, propositions, lemmas, and corollaries in the article
have analytic/algebraic proofs. The statements are not based on PSLQ or on
the numerical replay.

| Result | Article label | Status and proof dependency |
|---|---|---|
| Bilinear/scaled Laplace–Plancherel | `thm:plancherel` | Proved from Hermitian Plancherel and a scale substitution. |
| Basic compensated Hurwitz closure | `thm:basic` | Proved in an initial absolute-convergence half-plane, then holomorphically continued using the combined kernel. |
| Arbitrary Stieltjes indices | `thm:all-stieltjes` | Proved by holomorphic L2 parameter differentiation and explicit Laurent coefficient extraction. |
| Complex-safe Hermite formula | `thm:complex-Hermite` | Proved from the classical Hermite representation, with the paired complex integrand retained. No novelty claim for the classical representation. |
| Polygamma/harmonic pairings | `thm:polygamma`, `thm:harmonic` | Proved by exact kernel multiplication. |
| Lerch/polylog identities | `thm:lerch`, `thm:mixed-lerch` | Proved by partial fractions, confluence, and holomorphic cancellation. |
| Arbitrary compensation depths | `thm:Fd-domain`, `thm:depth-closure` | Proved by kernel vanishing orders, Gamma cancellation, and finite Mellin algebra. |
| Stirling norm and all normalized primitives | `thm:Omega-pair`, `thm:primitive-ladder` | Proved by a removable negative spectral value and a decaying primitive normalization. |
| Rational-scale residue grid and all jets | `thm:grid`, `thm:rational-depth`, `thm:rational-coeff` | Proved by a finite arithmetic decomposition and exact coefficient formulas. |
| Finite resonance evaluator | Section 9 | Its finite constant-term rules follow from the Gamma/zeta Laurent expansions and holomorphy proved earlier. |

## Evidence levels

1. **General analytic proof:** the article proves the infinite families with
   their precise domains and branch choices.
2. **Exact finite replay:** 538 rational/polynomial assertions verify selected
   valuations, zeros, residue cancellations, and lattice identities.
3. **Unvalidated numerical diagnostics:** 76 comparisons at 60 working digits,
   including genuinely independent vertical and Laplace quadratures.
4. **Dependency negative control:** the mpmath 1.3.0 complex Stieltjes problem is
   intentionally reproduced; the corrected routes are checked separately.

Neither levels 2 nor 3 alone proves the general results. No interval-certified
rounding analysis and no Lean verification are supplied.

## Not claimed

- A solution of S6 or revised S8.
- A complete audit of the canonical manuscript or all incoming ZIP contents.
- Priority over all historical literature for every identity.
- An algebraic-independence theorem for the constants appearing in a finite alphabet.
- Ordinary convergence outside the stated L2 product domains merely because a meromorphic right-hand side can be continued there.
- A defect in later/current mpmath releases based solely on the tested version 1.3.0.
