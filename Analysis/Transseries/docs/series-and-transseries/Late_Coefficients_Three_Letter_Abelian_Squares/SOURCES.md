# Sources and priority

Research date: 2 October 2026. This bibliography identifies the classical ingredients and bounds the novelty check. It does not claim an exhaustive literature search.

## Target and classical analytic sources

1. [OEIS A274600](https://oeis.org/A274600), contributed by Václav Kotešovec on 10 November 2016. The inspected entry explicitly labels the leading late-coefficient asymptotic as a conjecture, supplies the 1/(4N) normalization, and displays 22 coefficients. All 22 were verified exactly. The linked 0..80 b-file was not accessible through the tested routes, so no claim is made of direct agreement with all 81 b-file entries.
2. [OEIS A002893](https://oeis.org/A002893). The underlying three-letter abelian-square counts, moment identity, honeycomb-return interpretation, and recurrence are established background.
3. Jonathan M. Borwein, Armin Straub, James Wan, and Wadim Zudilin, [Densities of Short Uniform Random Walks](https://doi.org/10.4153/CJM-2011-079-2), Canadian Journal of Mathematics 64 (2012), 961–990, with an appendix by Don Zagier. Equations (1.2), (3.1), and (3.2) provide the classical elliptic density, the logarithmic singularity at radius one, and the connection to the same moments. [Author-hosted PDF](https://people.mpim-bonn.mpg.de/zagier/files/doi/10.4153/CJM-2011-079-2/borweinJ0395.pdf)
4. [NIST DLMF 15.8.10](https://dlmf.nist.gov/15.8.E10) supplies the convergent zero-balanced hypergeometric logarithmic expansion. [DLMF 15.12](https://dlmf.nist.gov/15.12) supplies the standard large-variable hypergeometric estimates.

The elliptic density, van Hove logarithm, Watson's lemma, keyhole coefficient extraction, and Lagrange inversion are classical. The note's contribution is the explicit proof and all-fixed-order/Stokes/inverse strengthening of the labeled late-coefficient assertion.

## Prior and related asymptotics

5. L. B. Richmond and Jeffrey Shallit, [Counting Abelian Squares](https://cs.uwaterloo.ca/~shallit/Papers/cas.pdf). The leading asymptotic of the original counts is established background.
6. Charles Burnette and Chung Wong, [Abelian Squares and Their Progenies](https://arxiv.org/abs/1609.05580), 2016. Broader asymptotic results for abelian-square-related classes.
7. [The 2016 Stack Exchange discussion linked by A274600](https://math.stackexchange.com/questions/2006632/sum-involving-the-product-of-binomial-coefficients). The located discussion treats the sum's leading asymptotic, rather than proving the late-coefficient conjecture.
8. Nino Bašić, Patrick W. Fowler, Barry T. Pickup, and Primož Potočnik, [Random walks and the electronic structure of graphene](https://doi.org/10.1063/5.0319282), Journal of Chemical Physics 164 (2026), 104103. Its inverse-bandgap expansion uses the original moments; it is distinct from the late coefficients studied here.

## Bounded duplicate check

- Exact-ID web searches combining A274600 with proof, asymptotic, factorial, ProveIt, and OEIS Open did not locate an existing proof
- Targeted searches of the ProveIt default branch for A274600, A002893, and honeycomb returned no matches
- Inspected complete Analysis, Combinatorics, and Oeis path listings contained no exact target-ID path; they had 5,850, 462, and 9 entries and were marked untruncated
- The repository root snapshot for this check was 4b874cea0012c51a6841ad9c58f6e20fa57c71da

These checks are not a full-text audit of every file or historical revision, and do not exclude differently indexed, unpublished, or overlooked prior work.

Only bibliographic links and check metadata are distributed here. Full third-party papers and webpage snapshots are not included in the replay package.
