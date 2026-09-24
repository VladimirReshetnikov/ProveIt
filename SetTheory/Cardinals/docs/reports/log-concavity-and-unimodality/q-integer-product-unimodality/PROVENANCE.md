# Source, priority and computational audit

Research dates: 18 September 2026 (general-product work) and 20 September 2026
(two-shift threshold work). Merged into a single package on 20 September 2026.

This file is the union of the provenance records of the two packages that were
merged: `PROVENANCE.md` of
`docs/reports/log-concavity-and-unimodality/q-integer-product-unimodality`
and `sources.md` of
`docs/reports/log-concavity-and-unimodality/binomial-smoothing-threshold`.
Where the two disagreed on how much may be claimed, the more cautious wording
was kept.

## Exact target

Brendan B. Connelly, Ezekiel Ito, Thomas C. Martinez, Olha Shevchenko, and
Kacey Yang, *Unimodality of q-Fibonomial coefficients for small cases*,
arXiv:2605.12822v1.

- Pinpoint: Section 5.2, Conjecture 5.4, printed/PDF page 14.
- Version-pinned record: https://arxiv.org/abs/2605.12822v1
- HTML: https://arxiv.org/html/2605.12822v1
- PDF: https://arxiv.org/pdf/2605.12822v1
- Current record checked: https://arxiv.org/abs/2605.12822
- Author project page: https://brendanconnelly.com/projects
- Another coauthor's research page surfaced:
  https://sites.google.com/g.ucla.edu/shevchenko/research

The statement was checked in HTML, in parsed PDF text, and visually: the
relevant PDF page was also inspected as an image. The necessity clause uses
**k <= 3 OR r <= 3**, not an intersection of those conditions, and its
`r <= 3` alternative covers the six-factor counterexample used here. The source
uses weak unimodality, so the central plateau of the counterexample is
admissible. Its reported tests stop at k <= 5, r <= 6, max(a_i, b) <= 15.

The arXiv submission history displayed version 1, submitted 12 May 2026,
as checked on 20 September 2026. The rendered article itself displays an
internal typeset date of 24 August 2026. This package identifies the source by
arXiv version rather than inferring version history from the internal date.

The source's own example `[3]_q^4 [2]_(q^4)` only disproves *unrestricted*
necessity, from outside the stated necessity range; it is not the example used
here. The r = 3, k = 6 example of this package lies inside that range.

## Background references

Nantel Bergeron, Cesar Ceballos, and Josef Küstner. *Elliptic and q-Analogs of
the Fibonomial Numbers.* SIGMA 16 (2020), paper 076, 16 pages.

- Publisher: https://sigma-journal.com/2020/076/
- DOI: https://doi.org/10.3842/SIGMA.2020.076

Used to identify the background q-Fibonomial question as distinct from the
auxiliary Conjecture 5.4 attacked here; not used as a substitute for any proof.

Richard P. Stanley. *Log-concave and unimodal sequences in algebra,
combinatorics, and geometry.* Annals of the New York Academy of Sciences
576 (1989), 500-535.

- Author's publication list, entry 72: https://math.mit.edu/~rstan/pubs/

Used for broad context on unimodality, convolution and log-concavity. The
specific convolution and log-concavity facts needed are proved directly in the
report.

## Mathematical scope

The counterexample refutes the necessity assertion in the stated auxiliary
conjecture. The sufficient half is *proved* in the report (Theorem 3.2), for
every spacing r >= 2 and every number of ordinary factors. Complete criteria
are given for r = 2 and r = 3, and a complete classification of the two-shift
family (1+q)^n (1+q^r) is given for every r >= 2.

The original main q-Fibonomial conjecture of the source paper is **not**
settled here; the counterexample addresses the product criterion, not a claim
that a particular q-Fibonomial coefficient is nonunimodal.

For r >= 4, no complete arbitrary-product classification is claimed, and the
necessity question for two or three ordinary factors at those spacings is not
settled. Restricting the source's necessity clause to surviving regimes would
be a new statement needing its own proof, not an automatic repair. Precisely:
necessity is true for r = 2 and for r = 3 with k <= 5, false for r = 3 with
t >= 6, and open here for k <= 3 with r >= 4.

For r >= 4 the members of the two-shift family at the threshold have both
k = n > 3 and r > 3, so they are *not* additional counterexamples inside the
conjecture's necessity range.

Two questions are left open by the merge itself: whether the wider
two-parameter family (1+q)^t [B]_{q^3} is log-concave throughout (the slice
B = 2 is), and whether the minimum-degree uniqueness persists at degrees ten
and above, where the finite search was not run.

## Searches and limitations

Among the queries actually used were:

- `"2605.12822" counterexample`
- `"Unimodality of q-Fibonomial coefficients"`
- `unimodality products q integers Connelly conjecture 5.4`
- `unimodality convolution shifted binomial distributions polynomial`
- `unimodal polynomial binomial two translates`
- `"unimodal" "r^2-3" binomial`
- `"unimodal" "(1+x)" "1+x^r"`

Further targeted searches examined the target paper and conjecture, the
two-translate binomial family, and exact-threshold formulations.

The target paper and author pages were found. No earlier correction of this
specific necessity assertion was located in the material returned. Several
broad or formula-heavy searches returned mostly irrelevant material, so this is
a limited search, not a systematic bibliography or a proof of historical
priority. In particular, no claim is made that all related work has been ruled
out, that the two-shift threshold theorem has not appeared elsewhere, or that
all auxiliary identities are absent from older probability literature. The
mathematical proofs are independent of the priority question.

The source authors were not contacted, and no external peer review took place.
Nothing here has been formalized in a proof assistant.

## Computational provenance

`data/verification_results.json` was generated by actually running

    python3 code/verify_products.py --full --out data/verification_results.json

The exhaustive and random ranges and the deterministic seed (1977) are recorded
in that file. That run also regenerates `data/certificate.json` and
`data/r3_binomial_thresholds.csv`.

`data/verification_report.json`, `data/thresholds.csv`, `data/degree_search.csv`,
`data/degree_summary.csv` and `data/counterexample.json` were generated by
running `python3 code/verify_threshold.py`. `data/minimal_certificate_output.txt`
records `python3 code/minimal_certificate.py`, and `data/symbolic_report.json`
records `python3 code/symbolic_checks.py` under SymPy 1.14.0.

All verifiers use exact integer coefficients throughout; no numerical root
calculation or floating-point tolerance is involved. All checks use explicit
exceptions rather than `assert`, so they remain active under `python -O`.
No network access is used by any verification program.

`code/verify_products.wl` was evaluated separately through the Wolfram
connector. Its returned kernel version (15.0.1 for Linux x86, 2 July 2026) and
exact output are retained in `data/wolfram_output.txt`. The two computer
algebra witnesses check the two *different* algebraic routes to the two-shift
threshold: Wolfram checks the base identity `4nn(2+nn-rr^2)` and the step
identity `4*nn*rr*(2+nn-rr^2+2ss+ss^2)` of the alternative proof, while SymPy
checks the free-n ratio identity, the central-difference identity and the
boundary factorization of the primary proof.

Both the CAS calculations and the finite tests are supplementary: neither
constitutes proof-assistant verification of the infinite statements. The
degree-at-most-nine search is the one exception in kind: its completeness is
proved in the report, so it does certify the stated minimum degree.

`data/area_selection.json` records the random area draw that started the
two-shift package: `secrets.randbelow` over 24 areas, realized index 0
(enumerative combinatorics), no redraw. The raw operating-system entropy was
not recorded, so re-running the draw is not expected to reproduce the index.
All mathematical calculations in the report are deterministic.

The PDF was compiled from the included TeX source and visually inspected
through page renders. Source font files are not included, and no external paper
or font file is redistributed in this archive. No checksum manifest is
distributed with this package.
