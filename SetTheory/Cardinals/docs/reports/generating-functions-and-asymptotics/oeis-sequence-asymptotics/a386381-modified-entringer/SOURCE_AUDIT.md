# Source and attribution audit for Report180

Review date: 3 October 2026. This is a bounded source and overlap review, not a
worldwide historical-priority certification. This summary distinguishes the
recorded source inspection from the package's finite exact computations.

## Official sequence records

The inspected [A386363 record](https://oeis.org/A386363) supplies the modified
Entringer triangle recurrence and credits Mikhail Kurkov, 19 July 2025.
The inspected [A386381 record](https://oeis.org/A386381) identifies its diagonal
and attributes a leading asymptotic equivalent and the numerical amplitude
25.574519628957467521537232312735336894... to Vaclav Kotesovec,
2 September 2025. The recurrence, leading scale, and posted decimal amplitude
are prior work; the article does not present them as new discoveries.

The 21 visible A386381 terms were transcribed and independently regenerated.
The linked [b-file](https://oeis.org/A386381/b386381.txt) could not be retrieved
by the attempted route. This is a retrieval limitation, not evidence that the
file is absent. Claims of agreement with the inspected official list are
therefore limited to those 21 terms; farther values are independently computed.

The inspected entry did not link a proof or exact connection formula for the
amplitude. Absence of a link in that record does not establish the absence of
such work elsewhere.

## Classical mathematical inputs

1. Jessica Millar, N. J. A. Sloane, and Neal E. Young, *A New Operation on
   Sequences: The Boustrophedon Transform*, Journal of Combinatorial Theory,
   Series A 76 (1996), 44-54.
   [Primary author-hosted paper](https://neilsloane.com/doc/Me211.pdf).
   Theorem 1 gives B(z)=(sec z+tan z)A(z). This transform is the central
   classical reduction, explicitly credited. Its application to the present
   input-output boundary relation gives the sequence-specific ODE.
2. Philippe Flajolet and Andrew Odlyzko, *Singularity Analysis of Generating
   Functions*, SIAM Journal on Discrete Mathematics 3 (1990), 216-240.
   [Primary author-hosted paper](https://algo.inria.fr/flajolet/Publications/FlOd90b.pdf).
   Delta-domain singularity transfer is classical machinery.
3. Philippe Flajolet and Robert Sedgewick, *Analytic Combinatorics*, Cambridge
   University Press, 2009, Chapter VI.
   [Author-hosted book](https://algo.inria.fr/flajolet/Publications/book.pdf).
   Logarithmic transfer and continuation hypotheses are standard inputs, not
   new techniques claimed by this article.
4. J. Ben Hough, Manjunath Krishnapur, Yuval Peres, and Balint Virag,
   *Determinantal Processes and Independence*, Probability Surveys 3 (2006),
   206-229.
   [Primary paper](https://doi.org/10.1214/154957806000000078).
   Spectral Bernoulli representations are classical. The article also derives
   the required normalized determinant product directly. Its positive Green
   operator K is distinguished from the correlation operator K(I+K)^-1.

Frobenius theory, Abel's Wronskian identity, Gronwall bounds, Volterra equations,
positive trace-class determinants, Lambert-W inversion, and interval arithmetic
are established methods. Attribution to them does not imply a claim that every
application-specific consequence has been located in the literature.

## Bounded overlap review

The source review recorded read-only exact-identifier and amplitude searches in
the live ProveIt repository and the available earlier-report collection. No
matching report was located in the inspected results. Ranked and fuzzy searches
and failed exact-ID queries are weak negative evidence; none establishes an
exhaustive absence theorem.

Actual nearby report README files were inspected, including:

- [A125054 central Poupard numbers](https://github.com/VladimirReshetnikov/ProveIt/blob/main/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a125054-central-poupard-numbers/README.md),
  concerning tangent moments, pole sectors, and related asymptotics
- A205497 zigzag-Eulerian spectra, concerning fence extensions and finite
  matrix spectra
- A122399 surjection diagonal, concerning a different pole/saddle problem

The first shares classical tangent/boustrophedon ingredients. The others concern
different exact objects. These inspected comparisons did not exhibit the
modified Entringer boundary ODE or the complete connection/marked package here.
Selected generic-title earlier reports were also inspected beyond search
snippets; that selection was not an exhaustive reading of the collection.

This package summarizes that bounded review; it does not claim the review was
independently repeated at every packaging step. Repository contents can change,
and unlocated antecedents or equivalent formulations may exist.

## Mathematical and computational evidence

The report supplies conventional arguments for the exact normalization,
positive/entire connection function, parameter-uniform Frobenius and transfer
theorems, trace-class construction on an infinite-measure space, determinant
identity, limiting Bernoulli law, weighted probability corrections, simple
limiting zeros, and controlled inverse brackets.

Independent exact computations checked marked triangle/ODE identities for
n=2,...,18, formal coefficients, and the degree-eight P_10 counterexample by
squarefreeness and Sturm variation. Independent normal and optimized runs
agreed. The scalar producer and interval-certificate calculation were also
reproduced from copied scripts with byte-identical recorded outputs in the
checked environment. The standard-library core adds its own finite exact
verification; README_CODE.md specifies its coverage.

The certificate's truncation inequalities were separately reviewed. The finite
interval operations still rely on the mpmath implementation. Reproduction does
not formally verify Python, SymPy, mpmath, or the operating system, and finite
diagnostic agreement does not prove the analytic theorems.

## Limits of the conclusions

- The marked statistic is defined by the recursive boundary marking. No
  external combinatorial bijection is asserted
- The limiting law is an infinite sum of independent Bernoulli variables;
  the finite P_10 counterexample rules out a general finite-polynomial
  Bernoulli representation for this marking
- Remainders are for each fixed order. Their constants and onsets are not
  computed as certified finite-N bounds
- The amplitude interval is separately certified by convergent-series tails
  and trusted interval arithmetic. Longer diagnostics are not all certified
- Near integer boundaries, an asymptotic inverse must be supplemented by exact
  evaluation. Simply taking its ceiling is not an unconditional rule
- Neither convergence of the full asymptotic expansion nor a complete
  exponentially small sector structure is proved
- No global novelty or open-problem-resolution claim follows from this review

Only article/package deliverables and relevant computational inputs are
distributed. Third-party PDFs, unrelated source material, and raw research or
review dossiers are excluded.

## Separate large-positive-real-mark theorem

A further conventional audit checked the Liouville transform, both endpoint
normalizations, the sign of the Bessel Green kernel, bounded relative Volterra
estimates including derivatives, and the final Wronskian constant. It supports
C(lambda)=exp(L sqrt(lambda))/(2 sqrt(2) pi sqrt(lambda))
(1+O(lambda^-1/2)) for real lambda tending to positive infinity, where
L=integral_0^rho sqrt(E(z)/z) dz. These are classical asymptotic methods.

The underlying modified-Bessel identities and endpoint/asymptotic facts are
credited to the NIST Digital Library of Mathematical Functions:
[I_nu definition, 10.25.2](https://dlmf.nist.gov/10.25.E2),
[K_nu integral, 10.32.9](https://dlmf.nist.gov/10.32.E9),
[Wronskian, 10.28.2](https://dlmf.nist.gov/10.28.E2),
[small-argument limits, 10.30](https://dlmf.nist.gov/10.30), and
[large-argument function and derivative expansions, 10.40.1-4](https://dlmf.nist.gov/10.40).

Independent smooth quadrature at 50, 100, and 150 digits supports the short
approximation L=4.2586174557. This is an ordinary diagnostic, not an interval
certificate; the exact theorem uses the integral definition. The package
includes only this quadrature script and its diagnostic JSON from that work.
It does not include the exploratory large-mark scripts or the audit dossier.
The theorem is separate from fixed-compact-mark N-asymptotics. No joint regime,
complex-sector theorem, Weyl expansion, or
numerically certified large-mark error constant is asserted. The bounded
attribution and non-exhaustive overlap qualifications above continue to apply.

## Far tail of the fixed limiting Bernoulli law

A final conventional audit establishes a leading mass asymptotic with relative
O(m^-1/2) error for the fixed limiting law, including the normalization

```
Pr(J=m) = L^(2m+1) / [sqrt(2) pi C(1) (2m+1)!]
          * (1 + O(m^(-1/2)))
K = L / [4 sqrt(2) pi^(3/2) C(1)]
```

Here K is the equivalent inverse-power/exponential carrier's prefactor.
The factorial comparison is asymptotic, not an exact factorial or
conditioned-Poisson representation. The audit also validates
Pr(J>=m)/Pr(J=m)=1+L^2/(4m^2)+o(m^-2) and a controlled rare-tail inverse
for n(y)=min{m>=0:Pr(J>=m)<=y}. Its rounding statement is a two-sided
ceiling enclosure; a single unconditional ceiling is not justified.

The inputs are the positive summable spectral product and the independently
audited large-positive-real-mark connection theorem. Classical exponential
tilting, Bernoulli characteristic-function estimates, Fourier inversion,
convex secants, and monotone-density estimates supply the argument. No novelty
is claimed for these methods. The countably infinite Bernoulli case and all
normalization factors were checked in that proof audit; the new theorem does
not rely on a differentiated asymptotic O-term or complex-sector WKB estimate.

No numerical or executable evidence is added for this theorem. Its error
constants and sufficiently-large onset are existential. The growing tilts
are of order m squared, so fixed-compact-mark finite-N convergence does not
justify a simultaneous finite-N/m rare-tail statement. No uniform finite-size
rare-tail theorem, all-orders tail expansion, effective numerical onset,
complex-sector theorem, or spectral Weyl expansion is asserted. The earlier
bounded source/overlap and conventional-proof qualifications remain in force.
