# Proposed integration: periodic collision contacts

## Placement

Suggested directory:

```text
Analysis/Polylogarithms/docs/reports/
  stieltjes-correlation-calculus/continuations/
    periodic-collision-contacts/
```

This is an unapplied research delivery. It has not changed the repository or the canonical manuscript.

## Precise editorial update

The preceding **Coincident-Point Stieltjes Calculus**, Section 11.1, asks for the delta-supported terms that compare a periodic convolution distribution with a specified extension of its off-point collision function. Mark the following restricted but all-index claim as proved by Theorem 5.1 of the delivered article:

> With separately defined scale-one coordinate Hadamard extensions of the factors and scale-one extensions in a and 1-a of the off-point correlation, their difference is exactly kappa delta^(p+q), with kappa given by the explicit gamma–harmonic coefficient formula. No lower delta derivatives occur.

The scope phrase about both coordinate conventions is essential. Do not shorten it to an unspecified “unique distributional extension.” Different extension prescriptions can change contact terms.

The compact `manuscript_insert.tex` contains the theorem and its calculation, using labels/macros prefixed with `pcc:`/`pcc`. It uses the canonical manuscript's theorem environment and standard AMS packages. It should be placed after the coincident/shifted Stieltjes material, not in place of the earlier off-point proof. Its opening paragraph refers to the full accompanying article for the analytic endpoint lemma and all downstream identities.

## Dependency chain

1. Hurwitz shift and Fourier formulas, plus the Stieltjes expansion convention.
2. Full-numerator local resonant subtraction on periodic smooth tests.
3. The separately completed single-factor family T_p(t).
4. The off-point separated generator, already present in the preceding report.
5. Completing that generator in the shift versus convolving the completed factors.
6. Contact coefficient extraction, its harmonic specialization, and Fourier moments.
7. Mean-zero antiderivatives; contact terms become explicit Bernoulli polynomials.
8. Ordinary primitive and log-Gamma covariance identities.

Theorem 5.1 and Corollary 6.1 in the full article are the key integration targets. The Fourier/polylogarithm and primitive theorems are additional exact consequences, not new unresolved conjectures.

## Preserve these statuses

The preceding off-point collision polynomial, analytic remainder, and scalar same-point finite constant are unchanged. There is no allegation of a false source theorem: that report explicitly reserved the distributional extension problem. The erroneous equation with the base atom omitted is deliberately presented as a rejected extension.

Do not promote S6, the revised S8, cubic same-point moments, arbitrary coordinate transports, unequal-grid/twisted products, or any uninspected incoming claim. No proof-assistant formalization, arithmetic independence, or global novelty certification is supplied.

## Verification distinction

The default finite replay passes 760 exact assertions and produces 420 coefficients. The 40 numerical diagnostics use 60-digit arithmetic and truncated convergent local series. They are not interval certificates. The full-index proof requires the local subtraction lemma and the distributional convolution calculation in the article; replay alone does not replace those arguments.

The PDF was compiled with three serial pdflatex passes and reviewed through rendered pages. The manifest pins the delivered artifacts, not a future regenerated PDF.

## Inspection scope

Observed main head during the run:
`dcd95baeb7c0e914b138bddef6829c5b1d52b726`.

The full preceding coincident TeX was read as a Library file. The matching named incoming ZIP was listed, but its bytes were not compared with that Library source. The other incoming archive contents were not fully audited. Repository references in the article are an inspection record, not a claim that every fetched main-branch file was retrieved by the same pinned revision.
