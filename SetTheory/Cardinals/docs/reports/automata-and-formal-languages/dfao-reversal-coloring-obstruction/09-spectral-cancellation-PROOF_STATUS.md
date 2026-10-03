# Proof and dependency status

## Objects kept distinct

- `D*_k(n)` is the explicit coloring/witness deficit, defined for n>=7 by an
  algebraic formula. It exists independently of any optimality theorem.
- `D_k(n) = k^n - R_2(n,k)` is the true optimal reversal deficit.
- The equality of these objects eventually is repository input **(O)**, not
  independently reproved in this package.

## Complete arguments supplied in the article

1. Signed palette expansion and independent positive Stirling formula.
2. Exact residue amplitudes in terms of integer moments T, U, V.
3. Minimality lemma for exponential-polynomial sequences on a tail.
4. Exact minimal residue polynomials, selected by nonzero moments.
5. Exact unit-step factors, including rational conjugacy at nonsquare products
   and the three Fourier-sector tests at square products.
6. Correct unit-root multiplicities; minimal order 9 for three outputs.
7. The k=19, p=12 cancellation, with three explicit signed coefficients.
8. Unique product-12 odd cancellation for all k>=7; no product-12 even-moment
   cancellations; all four product-12 full modes survive for all k>=7.
9. Parity-coherent noncancellation, including every product not divisible by 4.
10. Finite effectively computable exception sets for each fixed product, via
    nonzero leading coefficients of falling-factorial polynomials.
11. An elementary lower bound of order k^2/log k on recurrence degrees.
12. A subquadratic upper bound using the cited multiplication-table theorem.
13. Exact reduced tail denominators and finite formulas for tail numerators.
14. A terminating full-optimum-prefix algorithm and its complexity bound,
    conditional on the repository's explicit eventual threshold.

All proofs are mathematical proofs as written. None has been externally refereed
or checked in Lean, Rocq, Isabelle, or another proof assistant.

## Imported statements

- Repository input (O), for transfer to the actual optimum and for the finite
  bound on its initial correction. The source is itself an unrefereed research
  report. Removing this input leaves all witness-sequence results intact.
- Ford's published multiplication-table estimate for the improved asymptotic
  upper bound. The elementary O(k^2) upper bound and the lower bound do not
  depend on Ford's theorem.
- Classical finite-automaton minimization and reversal-orbit facts in the
  theoretical prefix algorithm; the relevant arguments are recalled.

## Finite computation

The exact output of `python code/verify.py` is in `data/audit.json`. In particular:

- Full and residue spectra were reconstructed independently from positive
  coloring counts for k=3,...,30 modulo two primes.
- The moment/support scan was finite: k=3,...,200.
- The totals 60,59,60,59 and full order 222 at k=19 use exact finite tests
  for every product class. Their records are in `data/spectra.json`.
- Product-12 uniqueness for all k is NOT inferred from the scan. Its proof uses
  explicit polynomial differences and integer sign crossings.
- The stored JSON assertion that the relevant product-12 polynomials have no
  additional nonnegative integer roots relies on that monotonicity proof,
  together with the finite arithmetic checks of its crossing inequalities.

## Not claimed or performed

- No exhaustive transition-pair search to determine the unknown initial
  nineteen-output optimum, or the complete finite prefix for general k.
- The finite-prefix algorithm is proved but not implemented by the included
  scripts and was not executed.
- No resolution of the entire two-parameter DFAO optimum, the diagonal monoid
  problem, or the classification of extremal transition pairs.
- No uniform classification of all cancellations in both k and p.
- No inference that the scan through k=200 implies full noncancellation forever.
- No claim that the degree-15 four-output polynomial is new.
- No claim of exhaustive literature priority.

## Reproducibility scope

The programs use only standard Python, arbitrary-precision integers, exact
fractions, and finite-field arithmetic. They raise exceptions rather than use
checks that disappear under `python -O`. There are no network calls and no
external CAS dependency. Their arithmetic is executable evidence, not a formal
verification of the Python interpreter or of the universal theorems.
