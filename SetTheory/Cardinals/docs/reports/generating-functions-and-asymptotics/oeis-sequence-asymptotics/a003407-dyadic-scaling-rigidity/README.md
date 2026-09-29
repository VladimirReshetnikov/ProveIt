# Dyadic Scaling Rigidity and Log-Periodic Growth of 3AP-Free Permutations

Research article prepared for Vladimir Reshetnikov, September 28, 2026.

## Read the article

`article.pdf` is the compiled article. `article.tex` is the complete editable
source, including its bibliography. The article develops the Ramsey / 3AP-free
permutation-counting direction represented in ProveIt.

The central result classifies every positive real scale c:

    log(theta(floor(c*n))) - c*log(theta(n)) = o(n)
    if and only if c is an integral power of two.

It follows from an exactly certified fundamental-period theorem for the
continuous growth profile. Every other scale has exponential gain and loss
on sets of positive lower natural density. For the split 3n = 2n + n, the
article supplies explicit all-t dyadic subsequences with factors (49/50)^n
and (21/20)^n. Further results give the full interval of subsequential growth
rates, finite-data enclosures, all ordinary empirical limit laws, logarithmic
averaging, and polynomial/geometric sampling. Eight research directions and a
proposed proof-assistant implementation route are included.

## Mathematical and verification status

This is an unrefereed research development, not an executed Lean formalization.
The general divide-and-conquer profile method is prior work of Hwang, Janson,
and Tsai. Nonexistence of a single exponential growth constant was proved by
Boon Suan Ho in 2026. The additional scale-rigidity and statistical deductions
are proved in the article; exhaustive literature priority is not claimed.

Sharma's published upper splitting theorem is an imported mathematical result.
The large count values are published OEIS A003407 data, not newly enumerated
values. The exact integer consequences of these data were checked independently.
The counts themselves were independently recomputed only through n=32, and
checked by direct permutation enumeration only through n=8. These distinctions
are preserved in the article and `SOURCE_AND_PROOF_AUDIT.md`.

The question whether theta(n) is increasing at every step remains unresolved
here. No claim of a sharp profile regularity theorem, exact extrema, a
probability density, non-D-finiteness, or a natural boundary is made.

## Package contents

- `article.pdf`, `article.tex`: compiled article and its source.
- `figures/profile_enclosure.pdf`, `.png`: figure assets; the PDF asset is
  needed when compiling the article.
- `verify.py`, `verification.json`: exact checks and the executed record.
- `data/counts.txt`: attributed numerical data for 0 <= n <= 200.
- `plot_profile.py`: optional figure regeneration.
- `SOURCE_AND_PROOF_AUDIT.md`: sources, theorem dependencies, and limits.
- `build.sh`: two-pass PDF build.
- `SHA256SUMS.txt`: hashes of the package files other than the manifest itself.

## Reproduce the checks

Python 3.10 or later, using only its standard library:

    python verify.py --max-n 32

The default is also 32. Do not use Python's `-O` flag: it disables assertions;
the script rejects optimized execution. The `--max-n` option accepts 0 through
36, but the included executed record uses 32. Increasing the limit can make
subset-state enumeration substantially more expensive. An output destination
can be selected with `--output PATH`.

The checks include 199 finite recurrence inequalities, the exact-period and
explicit-gluing certificates, root enclosures and extremizing indices for
three count bands, independent subset-state counts, and direct small
permutation enumeration. Finite recurrence checks do not prove the infinite
recurrence, and arithmetic checks on published counts do not certify their
enumeration.

## Rebuild the PDF

A standard LaTeX installation with pdfLaTeX and the packages listed in the
preamble is sufficient. No network access or bibliography processor is needed.
From the package directory:

    sh build.sh

Alternatively:

    pdflatex -interaction=nonstopmode -halt-on-error article.tex
    pdflatex -interaction=nonstopmode -halt-on-error article.tex

The figure is already included. To regenerate it, install NumPy and Matplotlib
and run `python plot_profile.py`. Plotting uses floating-point arithmetic; the
exact certificate checks do not depend on the plot or its numerical precision.

## Repository and data attribution

ProveIt was inspected at commit
`74f7f5bdba1aa728b340509701a0fa4e45e8dbf3`.
No repository files were changed and no full repository build was performed.

Numerical data source: OEIS A003407,
https://oeis.org/A003407/b003407.txt.
The table is attributed to Alois P. Heinz, with terms through n=90 from
Bill Correll, Jr., and Randy W. Ho. These are third-party published numerical
values; they are not claimed as original work of this package. The independently
written verifier uses the established subset-state enumeration idea, with its
correctness explained in the article.
