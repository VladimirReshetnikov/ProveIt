# Sources, scope, and audit notes

Consultation date: October 1, 2026 (America/Los_Angeles).

## Primary mathematical sources

1. Flórez, Ramírez, Villamizar (2024), *Restricted bargraphs and unimodal
   compositions*, JCTA 208, 105934.
   https://doi.org/10.1016/j.jcta.2024.105934
   Publisher HTML/search-indexed text supplies the class definition,
   generating-function decomposition, and Conjecture 2.3. The paper gives
   the area-100 ratio 1.9764206780767492582 and amplitude estimate
   0.6039015148966519. The article here rederives the decomposition rather
   than assuming a numerical generating-function fit.

2. OEIS A001523, weakly unimodal compositions / stacks.
   https://oeis.org/A001523
   Entry consulted directly. The known asymptotic credited to Auluck is
   NOT represented as new. The entry links the 2024 paper.

3. Flajolet and Sedgewick, *Analytic Combinatorics* (2009).
   https://sedgewick.io/books/analytic-combinatorics/
   Standard background for meromorphic coefficient extraction and
   analytic parameter perturbation. The report supplies the particular
   hypotheses and proofs needed for the target class.

## Repository review

Repository: https://github.com/VladimirReshetnikov/ProveIt
Tree SHA inspected: 29aca108ed25d714f31b1316512777fbbdc8e006.
Read: Analysis/Transseries/README.md.
Repository code searches for "bargraphs" and "A001523" returned no
matches. These were search-level checks, not a complete examination of
all archives, unindexed documents, or parallel uncommitted work.
No repository modifications or submissions to OEIS were made.

## Targeted literature searches

Searches included the exact paper title with "Conjecture 2.3",
"non-decreasing bargraphs" with "asymptotic proof" or "D-finite",
the target initial terms, and OEIS-focused searches for the class.
No matching prior proof of the selected conjecture or stronger pole
results was located in those searches. A failed search is not a proof
of novelty, and priority remains open to independent literature review.
No exact OEIS identifier for the area-counting target was verified.

## Explicitly unproved here

* That the positive real poles exhaust the complex pole spectrum.
* That the second positive pole is second-smallest in modulus overall.
* Simplicity or absence of cancellations at every nonreal candidate zero.
* Convergence of an infinite sum over all poles.
* A natural boundary at every point of the unit circle.
* Uniform fixed-level coefficient asymptotics when the minimum part grows.
* The leading term of the beyond-all-logarithmic-order pole correction.
* A unique canonical interpolation of the discrete sequence or an
  unconditional exact ceiling formula for its inverse.

These limits are also stated in the article and motivate further work.
