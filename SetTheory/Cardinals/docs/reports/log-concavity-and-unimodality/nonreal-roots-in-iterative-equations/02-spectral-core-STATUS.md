# Status and claim boundaries

## What is established in the written development

The article proves necessary and sufficient conditions on a monic real
polynomial with nonzero constant coefficient to be the exact minimal
iterative polynomial of an increasing homeomorphism of R. It gives an
explicit sharp universal reduction for every prescribed equation in that
class, exact affine-rigidity and fixed-point existence criteria, and analytic
realizations with specified nonreal multiplicities.

The proof uses the annihilator ideal, the minimal polynomial of the orbit
increment, bilateral recurrence decomposition, a two-ended positivity
argument, positive analytic interpolation, and conjugacy by an increasing
antiderivative. It does not assume the repository's circular classification
as an unproved premise. Standard real analysis and linear algebra are used.

## What is checked computationally

All arithmetic in the shipped verifier is exact rational arithmetic.
Two finite multiplicity grids contain 1,354 spectra in total. Exhaustive
enumeration examines 97,281 divisors and agrees with the core formula.
This is a check of the implementation and finite consistency of the formula,
not a proof of the spectral theorem for arbitrary spectra.

For two explicit scalar orbits, the code checks recurrences on -80 <= n <= 80,
402 increment/monotonicity assertions over -100 <= n <= 100, and nonzero
4-by-4 Hankel determinants. Their validity for all integer times and their
connection to actual real maps follow from the article's proofs, not from
the finite test range.

The extra fixed-point and affine-rigidity assertions in the verifier are
selected exact examples, not exhaustive tests of all dynamical criteria.

## What is not claimed

- No independent referee review or Lean/Rocq certification.
- No exhaustive historical-priority certification or claim that every
  proposed research topic is open throughout the literature.
- No classification of decreasing solutions, arbitrary proper-interval
  domains, noninjective equations with zero constant coefficient, or all
  individual maps realizing an admissible spectrum.
- No arbitrary-polynomial factorization algorithm in the supplied code.
- No implication that the numerical size of a finite test certifies the
  infinite or analytic portions of the proof.

The source repository was read only. This package is not a commit or an
update to the original repository.
