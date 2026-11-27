# Sharp Euler-factor agreement beyond prime exponent

Research deliverable for Vladimir Reshetnikov, 27 November 2026.

The complete argument is in `sharp_euler_agreement.pdf`; the standalone,
editable LaTeX source is `sharp_euler_agreement.tex`.

## Main results

For a cyclic group X of Dirichlet characters of order E, let p_1 < ... < p_s
be the distinct prime factors of E. For distinct multisets of k characters,
put t = min(s, floor(log_2(2k))). The exact minimum density of primes where
the **whole Euler polynomials** disagree is

    d_X(k) = product_{i=1}^t (1 - 1/p_i).

The result covers every E >= 2 and k >= 1. Prime powers in E do not change
the answer. The saturation density phi(E)/E is first attainable at
k = 2^(s-1). Explicit extremizers are given for every parameter.

Over all cyclic families, the exact minimum at degree k is the product
over the first floor(log_2(2k)) primes. It is asymptotic to
exp(-EulerGamma)/log(log(k)), and is attained even if every factor must
be primitive of one prime conductor.

For every nontrivial finite abelian p-group

    X = direct sum_i C_(p^a_i),  M = |X| / p^(min_i a_i),

the sharp cancelled-mass bound is delta >= (p-1)/(p*m). All its equality
cases are differences of full subgroup cosets separated by an actual
order-p element. The saturation floor is (p-1)/(p*M), first attained
at k=M. At every k=p^u the exact minimum is

    d_X(k) = (p-1)/(p*min(k,M)).

The finite theorems and the fixed-modulus density statements are unconditional.
The quantitative prime-window corollaries use Dirichlet GRH and the source
article's smoothed character estimate. The general order k^2 log^2 Q for
finding a distinguishing prime is an inherited scale, not a claimed new
detection exponent.

## Contents

- `sharp_euler_agreement.pdf`: complete research paper.
- `sharp_euler_agreement.tex`: standalone LaTeX, including bibliography.
- `code/verify_cyclic_euler.py`: exact cyclic packet, marginal and Fourier checks.
- `code/verify_pprimary.py`: exact prime-primary bounds and equality checks.
- `code/verify_all.py`: runs both suites and records their combined status.
- `data/`: deterministic JSON results and a recorded text result.
- `evidence/mathematical_review.md`: separate adversarial review of the proofs.
- `evidence/document_validation.json`: PDF layout and document validation record.
- `evidence/source_manifest.json`: hashes and pin of inspected source snapshots.
- `evidence/research_euler_manifest.json`: source metadata for current Euler papers.
- `SOURCE_AUDIT.md`: precise comparison with the requested repository and literature.
- `formalization.md`: a Lean formalization roadmap, not a completed Lean proof.
- `build.sh`: rebuilds the PDF with Tectonic or pdfLaTeX.
- `SHA256SUMS`: hashes of the deliverable files.

## Reproduce

Python 3.10 or later is sufficient for all verification; no third-party Python
packages and no network access are required.

```sh
python3 code/verify_all.py
```

This performs 10,417,835 exact unordered packet-pair comparisons, plus
signed-array, extremal-construction, equality-classification and cyclotomic
Fourier checks. The full run may take a few minutes depending on the computer.
Every comparison uses integer arithmetic or exact rational arithmetic.

To rebuild the PDF, use a working Tectonic installation with its document
bundle available, or a standard TeX Live/MiKTeX installation:

```sh
sh build.sh
```

The bibliography is embedded in the LaTeX file; BibTeX is unnecessary.

## Scope and provenance

Source repository: https://github.com/VladimirReshetnikov/ProveIt

Pinned commit: `6b034b74a8224c893e7e83127f33cd1a6958785d`.

The manuscript extends the article's explicit composite-exponent question
and the inspected unmerged prime-exponent papers. Worldwide publication
priority is not certified. Classical trade bounds, finite Fourier inversion,
Mertens' theorem and the source GRH estimate are credited as inputs.

No independent Lean kernel check of the new theorems is claimed. The exact
finite checks support the human-readable proofs; they do not establish the
infinite families by enumeration. Arbitrary mixed-primary noncyclic groups,
and all intermediate non-prime-power degrees below saturation in general
p-groups, remain outside the exact classifications here.
