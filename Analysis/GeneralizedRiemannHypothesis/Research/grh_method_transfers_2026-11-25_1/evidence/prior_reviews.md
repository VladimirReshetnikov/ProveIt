# Compact comparison of the five earlier reports

| Incoming archive | Substantial completed arguments claimed there | What remains open / boundary |
|---|---|---|
| `grh_transfer_analysis.zip` | Rank-sensitive determinant sandwich and completion cost; scalar one-sided Landau principle; conductor-23 cubic reduction; seven small algebraic Lean lemmas with recorded checking log | The principal-ideal-class prime inequality is not proved. Its finite-factorization Lean theorem assumes the analytic factorization. No nonabelian GRH result. |
| `grh_transfer_analysis_2026-11-25.zip` | Scalar pole criterion allowing higher-order poles with positive leading coefficient; sparse witness-family criterion with eta=(beta-1/2)/18; Tate inertia obstruction; products-before-gcds quantifier lemma | No construction of the sparse arithmetic family; degree-two target requires arithmetic and auxiliary-twist inputs; no Vandiver/K-group vanishing theorem. |
| `grh-transfer.zip` | Claimed 229-field abelian classification for Zhao's sufficient B_K<2 condition; small-prime n=xy+yz+zx representations; all-Galois completely-split one-sided criterion; exact upper limsup without linear independence | Enumeration has not been independently rerun this turn. The Kummer irreducible-prime inequalities are equivalences, not established bounds. The B_K test is sufficient, not a claimed characterization of all sign phenomena. |
| `grh-lean-transfers.zip` | Claimed 26 quintic CM coefficient fields and odd-prime-degree bijection; genus-field containment in every even weight; simultaneous quotient-group weighted races; signed S3 weights and fixed-periodic L2 obstruction | The prime-degree classifications are unconditional algebraic deductions, not internal transfers of the RH proof. No S3 zero theorem is obtained. No publication priority established. |
| `grh_transfers.zip` | Exponent-six completeness on omega(|D|)<=6 or |D|/P^+(|D|)<=1e8; mod-4 window positivity for every x>3/4; positive eta-product variance bound; conductor-23 sign equivalence | Does not prove the full exponent-six classification or conductor-23 RH. Explicitly asks whether intermediate genus subfields and small ramified ideals improve its exclusions; the new `genus_transfer.tex` answers this limited question. |

All packets use upstream commit `72fead102f663d5c7a407964a13dc0cf9d977207`
and distinguish its five Dirichlet-GRH/RH exports from general Hecke and
Artin conjectures. They cite independent upstream kernel records rather
than claiming a local full build. Detailed provenance and exact internal
file references are in `prior_reports.md`.
