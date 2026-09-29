# The Exact Logarithmic Degree of Hahn-Transseries Solutions

**Finite jets, Smith invariants, and cancellation-sensitive resonance**  
Research manuscript prepared for Vladimir Reshetnikov, 29 September 2026.

## Read

- `exact_logarithmic_degree.pdf`: the 29-page article.
- `exact_logarithmic_degree.tex`: standalone editable LaTeX source, including bibliography.

The article addresses the exact minimum promoted-logarithm degree and
cancellation-sensitive resonance questions explicitly posed in ProveIt's
*Finite Residue Obstructions and Logarithmic-Depth Promotion in Hahn Transseries*.

## Main results

For outer-small linear Euler perturbations over the specified real Hahn field
of logarithmic depth n >= 1, the article constructs a finite formal matrix series
M(z), with z acting as differentiation in the newly added logarithm T.
Its Smith exponents nu_i satisfy

    sum(nu_i) = r,       0 <= nu_i <= s,

where r is the sum of real-root multiplicities and s is the number of distinct
real indicial roots. They give the complete homogeneous degree filtration and
the minimum degree of every T-independent forcing. Finite block Toeplitz rank
tests give exact positive and negative certificates. Classification requires
only coefficients M_0 through M_(s-1), with explicit finite word-depth bounds.

A residue-weighted scalar subclass has the exact pencil M(z) = D_P(z I + B).
Every strictly upper triangular rational matrix B, hence every partition of the
operator order as a logarithmic-index profile, has an explicit finite rational
scalar realization. A fourth-order family distinguishes the correct weighted
cancellation data from both the unweighted graph and the nilpotency of M_0.

See Theorem 6.2 (classification), Theorem 7.1 (finite certificates), Theorem 8.1
(exact pencil), Theorem 9.1 (scalar realization), and Section 10 (cancellation).
Nine further research directions are developed in Section 13.

## Scope and status

These are conventional mathematical proofs, not a Lean formalization or an
independently refereed publication. Smith, Toeplitz, and Jordan-chain methods
are classical and are credited. Global priority is not established.

The theorem concerns solutions in H_n[T], with polynomial dependence on T.
Coefficients lower the outer x exponent by a uniform positive amount.
It does not assert analytic summability, classify arbitrary dependence on T,
or cover merely logarithmically small perturbations. Effective computation on
arbitrary Hahn data needs explicit coefficient-operation oracles; the finite
rational scalar realization with residue forcing does not have that obstacle.

## Exact verification

Python 3.10 or newer and SymPy are required. The recorded environment is
Python 3.13.5 and SymPy 1.14.0.

```sh
python -m pip install -r verification/requirements.txt
python verification/verify.py
python verification/operator_check.py
```

The recorded runs passed:

- 1,383 exact assertions in the primary algebraic suite.
- 192 exact projected-column checks in an independent noncommutative scalar
  differential-operator calculation, through jet degree 3 and word length 6.

The actual outputs are `verification/results.json` and
`verification/operator_results.json`. The primary suite includes rational
left-nullspace certificates for rejected degrees in the fourth-order example.
The arithmetic is exact; these are finite regression checks, not a verification
of all infinite Hahn-support arguments. No floating-point tests are used.

## Rebuild the document

With a standard TeX installation containing the packages in the preamble:

```sh
sh build.sh
```

The script runs pdfLaTeX three times and stops on an error. It needs no external
figures, bibliography processor, network access, or repository checkout.

## Additional files

`notes/proof_audit.md` records assumptions, key proof dependencies, and boundaries.
`notes/repository_provenance.json` records the inspected snapshot and source paths.
`notes/validation.json` records the PDF/build and verification checks.
`SHA256SUMS.txt` records hashes of the distributed files other than itself.

The repository snapshot is `76b8ea50cc67f2255c11b27e0edc9ed0fca3b5cd`.
No repository files were changed or uploaded.
