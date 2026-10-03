# Source and contribution audit

Audit date: 1 October 2026.

## Primary sources consulted

1. OEIS A205497, internal-format comments, current retrieved entry.
   https://oeis.org/A205497/internal
   The displayed old conjecture labels are not reliable evidence of current
   open status. The column-three numerator sign and numerator-degree indexing
   are specifically compared against the formulas derived in the article.

2. T. Kyle Petersen and Yan Zhuang, *Zig-zag Eulerian polynomials*, European
   Journal of Combinatorics 124 (2025), 104073; arXiv:2403.07181v4,
   submitted 9 September 2024.
   https://arxiv.org/abs/2403.07181
   https://arxiv.org/html/2403.07181v4
   Relevant: P-partition identity, gamma-nonnegativity, Theorem 3.15, and
   Conjecture 6.1. The HTML conversion's displayed “Date” is not used as the
   arXiv submission date; the version history supplies the version date.

3. Guoce Xin and Yueming Zhong, *Proving some conjectures on Kekulé numbers
   for certain benzenoids by using Chebyshev polynomials*, Advances in Applied
   Mathematics 145 (2023), 102479; arXiv:2201.02376v1.
   https://arxiv.org/abs/2201.02376
   https://arxiv.org/html/2201.02376v1
   Relevant: eigenvalue formulas, Section 5.2's column generating functions,
   Remark 5.7's observed cancellation, and Example 5.11's CORRECT +x^14 sign.
   The familiar product denominator, its degree, and its Perron growth
   constant are attributed to this existing work, not claimed as new.

4. OEIS A005586: a(u)=u(u+4)(u+5)/6, offset 0.
   https://oeis.org/A005586
   Used to diagnose the zero-based numerator-degree index shift.

5. OEIS A205493.
   https://oeis.org/A205493/internal
   Its index-14 value 546629054 independently agrees with the correct
   column-three generating function.

6. OEIS A050446.
   https://oeis.org/A050446
   Related weak alternating-word / order-polynomial array, with conventions
   translated in the primary papers.

7. Vladimir Reshetnikov, ProveIt repository README.
   https://github.com/VladimirReshetnikov/ProveIt
   Read through the connected GitHub tool. No theorem in an unverified
   repository research draft is a premise of the present proofs. Repository
   searches for specific candidate OEIS identifiers were not exhaustive.

## Additional results developed in this report

- Exact lcm minimality for all columns, including noncancellation of the
  highest pole at every shared eigenvalue.
- All-size gcd and primitive-factor first-occurrence classification.
- Totient formula and cubic asymptotic for the minimum recurrence order.
- Explicit size-uniform relative error, growing-index Perron asymptotics,
  the n/log n crossover correction, and growing-edge strict log-concavity.

These statements are supported by the manuscript proofs and checked in the
specified finite ranges. Their publication priority has not been independently
certified. The first three could have parallels in general transfer-matrix
or cyclotomic literature; the paper claims neither invention of those general
methods nor discovery of the known matrix spectrum.

## Claims intentionally not made

- No proof of full-row log-concavity, real-rootedness, simple roots, or Sturm
  interlacing of the zig-zag Eulerian polynomials.
- No assertion that all of the old OEIS conjectures are still open.
- No discovery claim for the already-published positive numerator sign.
- No Lean or other proof-assistant verification.
- No exhaustive repository review or exhaustive literature/priority search.
- No journal submission, OEIS edit, or GitHub write action.
