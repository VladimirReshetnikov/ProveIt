# Source, dependency, and novelty audit

Date of this report: October 1, 2026.

## 1. Repository provenance

Repository: https://github.com/VladimirReshetnikov/ProveIt

The snapshot inspected for the selected prior article was commit:

    1f1981f682b2878bde51a6ad40c22777f362fc05

The prior source is:

    SetTheory/Cardinals/docs/reports/
      generating-functions-and-asymptotics/
      oeis-sequence-asymptotics/a088714-bell-scale-growth/article.tex

Its Git blob identifier is:

    ccb50ef335ac4de27bd98a5a152fb48c978c7a96

Pinned source:
https://github.com/VladimirReshetnikov/ProveIt/blob/1f1981f682b2878bde51a6ad40c22777f362fc05/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a088714-bell-scale-growth/article.tex

The prior article, *Bell-Scale Growth of OEIS A088714*, is attributed there
to OpenAI ChatGPT and dated September 20, 2026. It proves

    log(a_n) = n log n - n log log n - n
               + O(n log log n / log n).

It explicitly leaves a finer Bell-number normalization conjectural and
notes that a root equivalent alone does not imply a consecutive-ratio
equivalent. The present article reproduces the growth proof, including the
Poisson comparison inequality, in Appendix A. Neither the prior source nor
the new article is assumed to have been formally verified or peer-reviewed.

Repository discovery and the selected source were inspected with the GitHub
connector. The earlier Library PDF of the September 20 report was also read,
and its page 8 was visually inspected to check the displayed comparison
recurrence. This was targeted inspection, not a theorem-by-theorem audit of
every file in ProveIt or its submodules.

## 2. External primary sources

1. OEIS A088714: https://oeis.org/A088714
   Defines the nonlinear series, lists the initial coefficients and reversion
   identities, and records its relationship to A088713. The displayed
   prefix through index 20 was checked exactly.

2. OEIS A088713: https://oeis.org/A088713
   Defines the companion series and its composition identity. The displayed
   prefix through index 21 was checked exactly. The separately linked
   300-term table was not treated as an independently checked input.

3. A. Nica and R. Speicher, *Lectures on the Combinatorics of Free
   Probability*, Cambridge University Press, 2006, especially Lecture 21.
   https://doi.org/10.1017/CBO9780511735127
   Standard source for the full-Fock-space/noncrossing-moment construction.
   The paper supplies the positive factorization and vacuum-word proof
   required for the present application.

4. Y. Wang and B.-X. Zhu, “Log-convex and Stieltjes moment sequences,”
   *Advances in Applied Mathematics* 81 (2016), 115–127.
   https://doi.org/10.1016/j.aam.2016.06.008
   https://arxiv.org/abs/1612.04114
   Prior general work on Stieltjes moments and infinite log-convexity.
   No novelty is claimed for that general implication.

5. M. Langer and H. Woracek, “Karamata's theorem for regularized Cauchy
   transforms,” *Proceedings of the Royal Society of Edinburgh A* 155(4)
   (2025), 1431–1491, first published online January 26, 2024.
   https://doi.org/10.1017/prm.2023.128
   General Tauberian context. A self-contained special-case proof with the
   exact sine constant appears in Section 8 of the new article.

6. Python Software Foundation, Decimal arithmetic documentation.
   https://docs.python.org/3/library/decimal.html
   Source for correctly rounded elementary operations used in the
   supplementary interval calculations. The actual interpreter used was
   Python 3.13.5; the computations do not depend on a web API.

The source pages were consulted during preparation on October 1, 2026.
URLs and identifiers specify the sources, not an assertion that those
sources already contain the new sequence-specific conclusions.

## 3. Bounded novelty assessment

Targeted searches paired A088714 and A088713 with terms such as “moment,”
“Stieltjes,” “Hankel,” and “golden.” The selected prior report and these
searches did not reveal the specific collection of results proved here.
This does not establish that no earlier work, alternate formulation,
unindexed source, or recent contribution contains any of them.

The sequence-specific deductions developed in this package are:

- a determinate positive-measure realization of both sequences via a
  moment-preserving nonlinear fixed-point transformation;
- strict positivity of all generalized Hankel minors and strict iterated
  log-convexity for these particular sequences;
- exact positive-axis Stieltjes-transform identities for the otherwise
  divergent ordinary generating series, and certified algebraic brackets;
- constant-one golden-ratio transform laws, explicit cumulative-mass laws at
  zero, and sharp negative-moment thresholds;
- consecutive-ratio equivalents, quantitative ratio bounds, and logarithmic
  far-tail equivalents using the inherited growth theorem;
- Fibonacci-ratio endpoint exponents for the algebraic approximants and
  certified enclosures on the exact inverse orbit.

The operator machinery, general moment inequalities, Tauberian principles,
and general renewal determinant identities are not advertised as new
inventions. The article gives their needed proofs so the sequence-specific
results can be checked without relying on numerical patterns.

## 4. Proof dependency map

Formal coefficient recursion -> compact positive operators -> coefficient
stabilization -> tight limiting measures.

Inherited growth theorem -> all positive exponential moments -> determinacy
and convergence of the full approximating sequences; it also rules out
bounded support.

Positive measures -> strict generalized Hankel positivity -> log-convexity
and its positive-measure iterations.

Compact analytic identities + weak convergence -> exact Stieltjes equations
-> inverse-composition identity -> golden-ratio rigidity -> explicit
Stieltjes Tauberian theorem -> mass laws at zero.

Log-convexity + inherited logarithmic growth -> consecutive-ratio laws ->
size-biased concentration and Markov bounds -> far-tail laws.

No step substitutes a divergent series into an analytic identity, infers an
infinite positivity statement from finite tests, differentiates a cumulative
mass equivalent to invent a density, or exchanges the approximation-stage
and large-argument limits without a separate argument.

## 5. Verification scope and remaining limitations

The complete exact test counts are in `data/verification.json`. The orbit
intervals are supplementary computational certificates conditional on the
written transform identities and the correctly rounded operations; their
rational seed and full endpoint strings are in `data/orbit_bounds.json`.
The article's asymptotic theorems do not depend on those finite intervals.

No Lean, Coq, or other proof-assistant verification was performed. There is
no claim of independent referee approval or certified priority. The eight
research questions are proposed next tasks, not a claim that each is an
already recognized unsolved problem in the literature.

In particular, this package does not establish absolute continuity, the
absence of every positive atom or support gap, a multiplicative tail
formula, a full coefficient equivalent, or the earlier finer Bell-number
normalization. The proved tail result is a logarithmic equivalent, and the
proved endpoint result concerns cumulative mass, not a density.
