# Research status and assumptions

## Contribution relative to the inspected drafts

The main new development of this continuation is the compact omitted-label
coding theorem (Theorem 5.1), followed by the non-Borel theorem (6.2), the
complete-metrizability classification (6.3), and closed-trace universality
(7.1–7.2). The bounded-image refinement and its closure trace are in Section 8.
This is a relative contribution statement, not a bibliographic-priority claim.

Earlier material is credited rather than claimed as new: the interpretation
atlas, general set-alphabet spectra, forward completion, support-core methods,
raw comparison of class well-orders, and uniform-family safeguards. Elementary
proofs needed for the continuation are repeated in the article.

## Mathematical dependencies

The principal set-level arguments assume ZFC and use:
1. kappa is an INFINITE INITIAL CARDINAL, not an arbitrary ordinal.
2. For the main coding: cf(kappa) = omega and |A| < kappa.
3. The classical perfect-set theorem for uncountable Borel Cantor subsets.
4. The complete-metric subspace/G_delta criterion, proved in Appendix A
   without a separability assumption.
5. For arbitrary closed Cantor traces: kappa > 2^aleph_0.
6. To identify prefix topology with order topology: thickness of the ordered
   alphabet, established for infinite surreal cardinal birthday cutoffs.

No CH, GCH, or large-cardinal hypothesis is needed for the main results.
The external inaccessible-universe example is separate. The birthday parameter
and the label cardinal 2^{<theta} must remain distinct.

The global arguments use the stated GBC setting or explicitly weaker elementary
comparison assumptions. Collections of class relations are virtual predicates
on class variables, not ordinary classes with classes as members. Families are
uniformly coded. Set-valued recursion is distinguished from ETR.

## Source inspection

Repository commit:
7ff7736ecf3a0adc8536b2d083cf819e1ba39ace

Inspected blob identifiers:
- report README: 4a60c55651c7fddba35441fe0283e6956f838551
- merged article: f3f69663cd63682ad2e1db808bcb3c6e8fd940ce
- SignSequence.lean: e2c093860f29b0b9ea312d50099fc4aa89a76a99

The README was read in relevant ranges; the merged article's opening and
provenance were inspected, not its complete proof collection. The first 230
lines of SignSequence.lean were inspected at the pin. The earlier manuscript
Surreal_Lexicographic_Orders_Prefix_Completions.tex was read for Question 13.1,
completion results, the two-sided-uniformity limitations, and the metric
criterion appendix. It is an unrefereed draft, not a journal source.

## Verification limits

No Lean build or kernel checking was performed. Proposed module names are a
formalization plan. Finite checks are regression checks only. No exhaustive
literature search or independent peer review is claimed. All mathematical
claims should be evaluated by their proofs and dependencies, not by the number
of finite assertions or their proximity to separately formalized repository
foundations.
