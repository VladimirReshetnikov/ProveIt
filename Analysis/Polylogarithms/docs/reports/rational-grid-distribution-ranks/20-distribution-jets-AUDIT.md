# Manuscript audit and proposed corrections

Scope: selected statements in Chapters 4, 7, 8, and 10 of the supplied manuscript. This is not a claim to audit every chapter or historical identity store. The pinned baseline and blob hashes are in `provenance.json`.

## 1. Uniform distribution rank — gap resolved for an explicit presentation

**Source:** `chapters/08-differentiation.tex`, label `tower:thm:rank`; related underived-grid discussion in Chapter 7.

The manuscript reports finite rank computations and explicitly says a uniform proof is absent. The source scripts are not imported, so the exact historical matrix layout is unavailable.

**Contribution:** define every prime/divisor row and prove rank q-phi(q), residual dimension phi(q)-1 after fixing the endpoint, for every denominator. The polynomial-weight proof is stronger: it works at all prime weights and under arbitrary finite jet specialization. Character coordinates alone would not have been enough; the article identifies the image of the entire relation map and supplies both spanning and independence in the formal quotient.

**Integration:** `integration/ch08_distribution_rank.tex`. Retain the formal-versus-numerical distinction. The claim is about the canonical matrix defined by the stated law, not a reconstruction of absent historical scripts.

## 2. Cubic log-gamma moment — literature/status correction

**Source:** `chapters/07-integration.tex`, label `integral:neg:cubic`.

The negative search in a small basket is legitimate as an experiment. The statement that finding a named Tornheim-type atom is still open is not accurate: Bailey, Borwein, and Borwein already evaluate the cubic moment using Tornheim–Witten derivatives in equation (11), Theorem 6 of their paper.

**Correction:** state the known formula, credit BBB, and keep further reduction to a smaller vocabulary as a separate research question. Do not describe the formula as newly discovered by this contribution.

**Integration:** `integration/ch07_cubic_correction.tex` and `integration/bibliography_addition.tex`. The article's Appendix A supplies a Fourier derivation, with convergence justification. Its occurrence of double zeta is explicitly distinguished from Hurwitz zeta.

## 3. Mixed-point antisymmetry — argument swap is essential

**Source:** `chapters/04-depth.tex`, paragraph beginning “The consequence is structural” after the symmetric Gaussian stuffle formulas.

The relevant paired involution is (a,b;x,y) -> (b,a;y,x). It is not an index swap with the argument pair fixed. At mixed arguments, equal indices do not force the complementary antisymmetric difference to vanish.

**Correction:** distinguish equal-argument from mixed-argument points. The article proves

    Im(Li_{2,2}(-1,i) - Li_{2,2}(i,-1)) > 0

by a strictly positive integral. Nonzero is not the same as independent of single-value products; no such independence is asserted.

**Integration:** `integration/ch04_mixed_involution.tex`.

## 4. S4 status — preserve the conjectural label

**Source:** `chapters/04-depth.tex`, label `gauss:eq:S4-closed`.

No flaw in the numerical candidate was established. Instead, the contribution proves a finite proof-search obstruction: the target is not in the span of the specifically declared 96 weight-five product shuffle/stuffle rows, even with their linear regularizations. The witness is zero on all single-value product atoms and pairs to 768 with the target.

This does not imply that the identity is false or unavailable from a richer double-shuffle system. The independent integral residual is numerical evidence only.

**Integration:** optional `integration/ch04_S4_status.tex`; exact matrix and witness in `certificates/s4_rowspace_obstruction.json`.

## 5. Numerical implementation note

During development, naive tiny-step differentiation of a polylogarithm evaluator near integer spectral order gave an unreliable first trace derivative. The final numerical program instead uses the pole-cancelled Hurwitz Fourier formula proved in the article. This is a local computational diagnostic, not a generalized bug claim about arbitrary library versions. All delivered numerical residuals come from the corrected evaluator.
