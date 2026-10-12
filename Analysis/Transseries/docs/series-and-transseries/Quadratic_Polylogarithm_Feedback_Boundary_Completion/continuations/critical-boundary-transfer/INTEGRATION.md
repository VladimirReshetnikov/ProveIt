# Proposed integration and source crosswalk

## Placement

File this package, after review, under:

    Analysis/Transseries/docs/series-and-transseries/Quadratic_Polylogarithm_Boundary_Transfer/

Add a cross-link from the Polylogarithms index. The package introduces no
Lean files and should not increase any formalization-coverage count.

## Relation to the inspected predecessor

Predecessor: *Resonant Polylogarithm Transseries: Gamma Borel Kernels,
Cyclotomic Order Jets, and Sharp Dilogarithm Reversion* (11 October 2026).

| Earlier item | New statement | Exact scope of update |
| --- | --- | --- |
| Section 12, Question 1: strict quadratic boundary law | Theorem 5.1, supported by Proposition 3.1 and Lemma 4.1 | Proves the proposed constant for every real s>2, u>U_c(s), including integer logarithms and unique complex dominance. |
| Same question: critical 2<s<3 | Theorem 6.1 and Corollary 6.3 | Gives the convergent two-generator chart, exact finite ramification and the coefficient constant. |
| Same question: marginal s=3 | Theorems 7.1–7.2 | Gives the Lambert normalization and every fixed inverse-logarithmic coefficient order. |
| Same question: finite curvature s>3 | Theorems 8.1–8.2 | Proves the leading law, convergent noninteger chart, and integer logarithmic obstruction. |
| Positive finite formula and Theorem 9.1 interior fold | Restated/credited only | No claim to replace or discover these earlier results. |
| Joint large-core/large-sector and moving-order questions | Further research section | Not marked solved. |

## Suggested editorial note

A ready-to-adapt LaTeX fragment is in `integration_note.tex`. Its meaning is:

> The fixed-parameter boundary regimes proposed in this question are proved
> in *Critical Boundaries of Quadratic Polylogarithm Feedback* (12 October
> 2026), Theorem 1.1, with proofs in Sections 3–9. The proof includes integer-order logarithms,
> unique complex dominance, and an all-order marginal logarithmic expansion.
> The joint limits in the core and order parameters remain separate questions.

This is a proposed cross-reference to a new unrefereed manuscript, not a
claim that an already-accepted source theorem was false. Preserve the
original open-question wording and attach the editorial note, rather than
silently rewriting historical delivery files.

## Review gates

First review the quadratic lift, finite coefficient identity, and exact
master equation. Next review the positivity/strict-circle continuation and
integer-order transport. The two critical charts, the Lambert/Gamma
compiler, and the finite-prefix extension can then be checked separately.

The Library predecessor was not byte-verified against its incoming ZIP
member. Before editing a filed source, identify that source's actual path
and confirm the intended article by title, equation and question. No patch
against an inferred archive-member path has been fabricated.

The code supplies finite exact regressions and floating diagnostics, not
interval proofs. All-order identities and complex continuation remain
conventional mathematical proofs in the manuscript. No remote changes
were made during preparation of this package.
