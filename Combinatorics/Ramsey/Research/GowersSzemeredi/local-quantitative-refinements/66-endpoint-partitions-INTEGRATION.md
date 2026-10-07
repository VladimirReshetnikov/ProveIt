# Integration crosswalk

Suggested standalone destination:

`Combinatorics/Ramsey/Research/GowersSzemeredi/endpoint-partition-normal-forms/`

All LaTeX theorem, equation, and section labels carry the `epnf:` prefix.
The article has its own bibliography and compiles without other repository files.
No existing source or proof-status ledger has been changed.

| Existing interface | This article | Scope |
|---|---|---|
| Gowers Section 7, unnumbered energy maximum before Theorem 7.2 | Theorems 4.1, 7.2, 10.2 | All-defect endpoint classification; sharp local envelope; first four ordered energy levels |
| Source 45, unit-Schur-defect lemma | Theorem 4.1 | Every integer defect r in the range n >= 3r+1; p(r) exact classes |
| Source 45, first gap and second equality cases | Section 8 | Credited background, reproved; not a new claim |
| Source 45, third-level lower bound and example | Theorem 9.1 | Complete equality classification for m >= 8, including the two-sided-hole class |
| Beyond the third energy level | Theorems 10.1 and 10.2 | Complete fourth equality classification for m >= 11 |
| Gowers Theorem 7.2 / Proposition 7.3 | Corollary 11.1 | Stronger whole-set conclusion, but only in a much narrower near-maximum energy window |
| Graph arising after the inverse step | Corollary 11.3 | Torsion-free graph rigidity; cyclic use needs additional rectification |

## Proposed formalization

A fresh namespace such as `GowersSzemeredi.OrderedEnergy` could contain the
finite counting arguments without importing the analytic inverse theorem.
Proposed declaration names and a proof dependency graph are in Appendix B.
They are specifications, not existing or compiled Lean declarations.

Recommended order:

1. Natural-valued ordered triple defects and the energy recurrence.
2. Positive Schur defects; consecutive zero defects force an arithmetic prefix.
3. First-failure lattice argument; first-failure two-hole exclusion.
4. Partition and endpoint-hole equivalence.
5. Exact boundary-hole energy with overlap correction and the kappa envelope.
6. Prefix classification and the third/fourth energy equality cases.
7. Torsion-free and no-wrap transfer interfaces.

The exact Python verifier is useful for regression testing but is not a
substitute for a proof-assistant verification. The research article must remain
marked unformalized until separate declarations have actually been checked.

## Non-claims to retain during merging

- n >= 3r+1 is the proved Schur threshold; n >= 2r+2 is only a conjecture.
- The third equality cutoff is m >= 8; the fourth is m >= 11.
- Endpoint defect r and total energy defect D(A) are different parameters.
- The first gap has published provenance and is also prior repository material.
- The fifth energy level is not established.
- Finite cyclic groups need a lifting/rectification hypothesis.
- No global Szemerédi or Ramsey bound has been improved by this article alone.
