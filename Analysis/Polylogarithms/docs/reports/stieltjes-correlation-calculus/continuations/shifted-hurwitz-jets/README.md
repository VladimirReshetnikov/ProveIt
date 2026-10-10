# Shifted Hurwitz-Zeta Correlations

**Exact Stieltjes Closure, Polygamma Contact Terms, and Log-Gamma Antiderivatives**

Research continuation for Vladimir Reshetnikov's ProveIt programme, dated October 10, 2026.

## Main deliverable

`article.pdf` is a 21-page article. Its complete LaTeX source is `article.tex`, `sections.tex`, and `references.tex`. The article contains self-contained analytic proofs, explicit specializations, a source audit, and six further research directions.

The main results are:

1. **All-index linear Stieltjes closure (Theorem 5.1).** For a nonzero shift, every canonical finite-part correlation of two generalized Stieltjes functions reduces linearly to single Stieltjes functions. One finite gamma-quotient coefficient formula gives every correction. The leading index is m+n+1; index m+n is absent.
2. **Differentiation contact law (Theorem 6.1; Corollary 6.2).** Periodic finite-part extension and pointwise differentiation differ by explicit delta derivatives with harmonic/elementary-symmetric coefficients. Every shifted polygamma product consequently reduces to first spectral Hurwitz-zeta derivatives.
3. **All-order ordinary-integral lifting (Theorem 7.3).** Correlations of normalized primitives of any positive integer orders reduce to Hurwitz-zeta jets at a single negative spectral integer. These are ordinary convergent integrals.
4. **Log-Gamma identities (Theorem 8.1; Corollary 8.2).** The translated log-Gamma product is evaluated using first and second spectral Hurwitz derivatives at -1, with an equivalent polylogarithm-order-derivative formula. A mixed log-Gamma/digamma integral reduces to second Hurwitz derivatives at zero.

For example, with 0<a<1 and the exact cutoff convention in Definition 2.1,

    FP integral_0^1 psi(x) psi({x+a}) dx
      = gamma_1(a) + gamma_1(1-a) - pi^2/3.

Ordinary differentiation of this finite-part identity without its contact correction is invalid. The corrected first derivative is Equation (6.6):

    FP integral_0^1 psi(x) psi'({x+a}) dx
      = J_00'(a) + psi'(1-a).

## Proof and novelty status

The analytic proofs, not the numerical checks, justify the identities. Classical Fourier, Hurwitz, Kummer, gamma, and Bernoulli facts are credited in the article. Global priority for every specialization has not been established. There has been no independent peer review, proof-assistant formalization, or interval certification.

This report does not solve the repository's S6 or S8 conjectures, prove period independence, or supply a same-point collision regularization. It does not present the existing pointwise Stieltjes derivative tower as erroneous.

The concrete source wording correction concerns requiring unknown Q-independence of a search basket. The distributional contact warning is a new extension guard, not an allegation that the manuscript already asserted an incorrect periodic theorem.

## Reproduction

Tested with Python 3.13.5, mpmath 1.3.0, and SymPy 1.14.0:

    python -m pip install -r requirements.txt
    python code/identity_engine.py --max-total 6
    python code/verify_numerically.py --dps 50
    python code/build.py

The last command requires `pdflatex` and the packages in `article.tex`. It compiles in an isolated temporary directory, runs three passes, and writes a build report. A Makefile provides equivalent targets.

The full numerical run completed **64 checks**, including six finite-cutoff diagnostics at epsilon=1e-18. All passed their individually recorded tolerances. The cutoff residuals include truncation error and are not interval certificates. The exact engine generated **28 ordered Stieltjes identities** through total index six, checked their reflection, weight, and linearity, and checked **35 primitive recurrences** plus the contact coefficients through derivative order eight.

`--quick` omits four Stieltjes cutoff quadratures; it was not used for the delivered final record. Numerical timings and PDF metadata can change upon replay; byte-for-byte reproduction of regenerated files is not asserted.

To verify delivered files without regenerating anything:

    python code/checksums.py --verify

To regenerate the manifest after intentional changes:

    python code/checksums.py

## Layout

- `article.pdf`, `article.tex`, `sections.tex`, `references.tex`: article and source.
- `code/identity_engine.py`: exact coefficient and primitive engine.
- `code/verify_numerically.py`: independent numerical diagnostics.
- `code/build.py`, `code/checksums.py`: document build and integrity tools.
- `data/exact_identities.json`: 28 exact reductions and first-primitive lifts.
- `data/numerical_validation.json`: all numerical values, residuals, tolerances, and versions.
- `data/theorem_status.json`: result/dependency/status ledger.
- `data/source_snapshot.json`: observed upstream hashes and inspection limitations.
- `data/build_status.json`, `data/build.log`, `data/pdf_review.json`: production receipts.
- `integration/`: placement instructions, audit notes, a periodic-extension note, and a guarded patch generator.
- `SHA256SUMS`: hashes of the delivered members.

## Integration

Proposed destination:

    Analysis/Polylogarithms/docs/reports/shifted-hurwitz-jet-correlations/

No repository files were changed. Incoming inventory and intake guidance were reviewed, but not every archive was read or mathematically audited. See `integration/README.md` and `integration/AUDIT.md`. The ZIP is suitable for delivery to `docs/incoming`; archival intake and code replay should remain separate from canonical mathematical acceptance.

No third-party source PDFs or standalone font files are bundled.
