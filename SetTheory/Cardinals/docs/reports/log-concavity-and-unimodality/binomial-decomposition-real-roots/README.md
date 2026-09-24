# Canonical Binomial Decomposition Does Not Preserve Real Roots

**Research manuscript and reproducible certificates — 20 September 2026**

The package gives a negative answer to Question 3.10 as formulated in
Lili Mu and Volkmar Welker, arXiv:2503.24076v1 (31 March 2025).
The problem concerns their specific canonical ("recursive") decomposition
`F(t) = G(t) + t H(t)` based on the integer binomial expansion of every
coefficient. The word *recursive* names that particular arithmetic rule, not
an arbitrary choice of `G` and `H` with `F = G + t H`.

This directory is the merger of two independently written packages that
answered the same question by the same proof program,
`mu-welker-binomial-decomposition` (the spine used here) and
`recursive-binomial-real-rootedness`. See "Provenance" below.

## Main results: two witnesses, both kept

The smallest counterexample there is:

    F(t) = (1+2t)(1+3t)^2 = 1+8t+21t^2+18t^3
    G(t) = 1+7t+15t^2+8t^3,   discriminant -59
    H(t) = 1+6t+10t^2,        discriminant -4,  zeros (-3 +/- i)/10

The smallest counterexample with three *distinct* input roots, which removes
"repeated roots caused it" as an explanation:

    F(t) = (1+2t)(1+3t)(1+4t) = 1+9t+26t^2+24t^3   (roots -1/2, -1/3, -1/4)
    G(t) = 1+8t+19t^2+11t^3,  discriminant -31
    H(t) = 1+7t+13t^2,        discriminant -3,  zeros (-7 +/- i*sqrt3)/26

In both cases both outputs have nonreal zeros. These are finite elementary
counterexamples, not conclusions drawn from approximate root finding.

The manuscript also proves:

- No counterexample exists in degrees one or two, so three is the minimum
  possible failure degree.
- Among cubics, 8 is the least linear coefficient of a counterexample
  (witness `(8,21,18)`, repeated root) and 9 the least among counterexamples
  with distinct input roots (witness `(9,26,24)`). Both are certified only
  within cubics, not across all degrees.
- For `(1+m*t)^3`, `G` is real-rooted exactly at `m=1,2,6`, and `H` exactly
  at `m=1,2,4,6`. In particular both fail for every `m>=7`. A transfer lemma
  shows `H` failing forces `G` failing in that family; an explicit example
  shows the converse is false in general.
- For `(1+2*m*t)(1+3*m*t)(1+4*m*t)`, the quadratic output is real-rooted
  exactly at `m=3,4`. The input roots are distinct for every `m`. A general
  open-region criterion `9(d-1)^3 e3^2 > 2(d-2)^3 e2^3`, i.e. `B^3 < 36 C^2`
  for cubics, has this family as one instance.
- Two explicit all-degree thresholds, neither implying the other. For each
  `d>=3`: the second output of the repeated-slope input `(1+m*t)^d` fails the
  first Newton inequality for every `m >= 20*(d-1)`; and the second output of
  the distinct-root consecutive-slope input `prod_{j=0..d-1}(1+(n+j)t)` fails
  it for every `n >= 10*d^3`.
- A two-sided coefficientwise scaling limit. Under dilation the second output
  converges to a transform `Q_F` that itself violates the Newton inequality,
  while the first output converges back to the input, so the first output
  eventually regains distinct real roots and the second never does.
- A compressed simplicial complex on 8 vertices whose deletion and link at
  vertex 1 are exactly `G` and `H` of the first example, while the same input
  also has a multipartite realization all of whose links are real-rooted:
  the failure is local and is not visible in the f-vector.

The exact theorem statements distinguish uniform explicit bounds from
proved eventual statements. The results do NOT resolve the Bell–Skandera
simplicial-complex realization question (Mu–Welker Question 1.1) or
Mu–Welker Conjecture 3.8; Proposition 3.9 there is the bridge between those
two, and nothing here bears on it either.

## Files

- `article.pdf`: the compiled 32-page article.
- `article.tex`: LaTeX source; it reads the three small `.tex` tables in `data/`.
- `README.md`, `REFERENCES.md`, `STATUS.md`: this file and the two provenance
  documents, both of which are retained because neither contains all of the
  page-level source audit, the enumerated searches, the journal-metadata
  caveat and the `f_{i-1}` versus `a_i` indexing correspondence.
- `references.bib`: BibTeX record for reference-manager import. The LaTeX
  bibliography is inline, so BibTeX is not required to build.
- `Makefile`: verification and PDF build targets.

Verification stack one (core, top level):

- `verify.py`: core standard-library verifier and table generator.
- `minimal_certificate.py`: independent short check of both main examples.
- `independent_sympy_check.py`: optional independent symbolic/Sturm check.
- `verification_report.json`: machine-readable results of the included run.
- `verification_output.txt`: console output of the core run.
- `minimal_certificate_output.txt`: output of the independent short checker.
- `independent_sympy_output.txt`: output of the optional symbolic checker.
- `data/cubics_a_le8.csv`: all 124 admissible inputs in the proved finite
  cubic search domain (with `b >= 3`), with their outputs and exact discriminants.
- `data/repeated_cubic_family.csv`: repeated-root cubic family through m=1000.
- `data/simple_cubic_family.csv`: simple-root dilation family through m=1000.
- `data/higher_degree_certificates.csv`: exact dyadic Newton witnesses for d=3,...,20.
- `data/*_table.tex`: generated article tables.

Verification stack two (wide scan, shares no code with stack one):

- `code/verify_wide.py`: independent reimplementation carrying the wider cubic
  scan, the colex-prefix recomputation of the splitting operator, the
  Sylvester-determinant discriminants and the all-degree certificates.
- `code/certificate.py`: 20-line standalone disproof driven from the literal
  digit table of the simple-root example.
- `code/verify.wl`: the exact input evaluated in a connected Wolfram Language
  kernel (reported version 15.0.1).
- `results/cubic_counts.csv`, `results/cubic_failures.json`: the A <= 14 scan
  (18,794 candidates, 3,159 real-rooted inputs, 25 failures) and the complete
  failure list.
- `results/all_real_rooted_cubics_A_le_8.csv`: the same 124 rows as
  `data/cubics_a_le8.csv`, produced independently, with both output discriminants.
- `results/all_degree_certificates.csv`: 294 all-degree Newton certificates,
  3 <= d <= 100 at n in {10d^3, 10d^3+1, 20d^3}.
- `results/compressed_complex.json`: the explicit complex with f-vector
  (1,8,21,18), deletion vector (1,7,15,8) and link vector (1,6,10).
- `results/examples.json`, `results/verification.json`, `results/verification.log`:
  the recorded run of `code/verify_wide.py`.
- `results/wolfram_output.txt`: the exact text returned by the Wolfram kernel.

No checksum manifest is distributed with this package, and none should be added.

## Reproduce the arithmetic

Python 3.10 or later is sufficient for the core work. No third-party Python
package, internet connection, numerical root finder, or floating-point
arithmetic is required. Checks raise rather than assert, so they are not
disabled by `python -O`; both ordinary and optimized runs were executed.

```sh
python verify.py
python minimal_certificate.py
python code/certificate.py
python code/verify_wide.py --out reproduced_results
```

The included core run checked 21,105 binomial expansions using two separate
implementations, all 621 cubic candidates in the proved bounds, both cubic
families through m=1000, and the explicit all-degree threshold `m = 20(d-1)`
for d=3,...,200. The recorded wide-scan run checked 40,008 expansion/Pascal
identities, 2,509 independent colex-prefix counts, 84,575 real-rooted
quadratic inputs, 18,794 candidate cubic triples, 294 all-degree certificates
and 6 Sylvester-determinant discriminants, in about 1.28 s on Python 3.13.5
(an observation about that run, not a portable performance claim).

The infinite theorems are proved in the article; these finite extensions do
not substitute for those proofs. Failure of the first Newton inequality proves
non-real-rootedness, but satisfying it proves nothing, so a nonpositive margin
in any certificate file is not evidence of real-rootedness.

A longer finite sanity check is available:

```sh
python verify.py --family-limit 10000
```

The core verifier's output directory defaults to the script's own directory; a
different location can be selected with `--output-dir PATH`. Running it
regenerates its CSV files, article tables, and JSON report. It does not
rebuild the PDF or change the included console transcript automatically.
`code/verify_wide.py` defaults to `--max-a 14` and, without `--out`, writes to
`results/` and replaces the recorded data there.

The optional SymPy cross-check requires SymPy, which was version 1.14.0 in the
included run:

```sh
python independent_sympy_check.py
```

This script does not import the core verifier. It independently checks all
621 input polynomials and the 248 outputs of the 124 admissible inputs using
exact square-free parts and Sturm root counts, and checks the canonical
expansions by a separate linear-search routine.

All polynomial coefficient lists in JSON and CSV are in ASCENDING power order.
Zero trailing coefficients may be retained in a decomposition list; they are
removed before classifying a polynomial's degree.

## Rebuild the article

The existing PDF is ready to read. To compile the source, use a standard
LaTeX installation with the packages listed in its preamble (including
`amsmath`, `amsthm`, `lmodern`, `microtype`, `booktabs`, `listings`, `hyperref`,
and `cleveref`). No shell escape or external graphics are needed.

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error article.tex`
several times until cross-references stabilize. The generated table files
must remain in the `data` subdirectory. The Makefile offers `pdf`, `verify`,
`verify-wide`, `minimal`, `certificate`, `symbolic`, `rebuild`, and `clean`
targets. The last compile produced 32 pages with no overfull or underfull
boxes and no LaTeX or pdfTeX warnings.

## Provenance

This package merges two research packages prepared on the same day for the
same question. `mu-welker-binomial-decomposition` is the spine: its section
skeleton, notation (`kappa_k`/`R_k`, `F`/`G`/`H`) and macros are used
throughout, and its article, verifier and data tree are the base.
`recursive-binomial-real-rootedness` supplied the explicit `n >= 10 d^3`
threshold for the distinct-root family, the open-region dilation criterion,
the wider cubic scan and the simple-root minimality statement, the
deletion–link and compressed-complex chapter, the operator-confusion warning,
the compact `M_{d,n}` certificate, the standalone digit-table certificate, the
Wolfram cross-check, and the colex/Sylvester/quadratic-scan checks. Both
proved the shared core theorem the same way: the same three integer binomial
expansions, the same two discriminant pairs, the same hockey-stick uniqueness
argument, the same k=2 and k=3 estimates, the same Cauchy–Schwarz proof of the
first Newton inequality, the same leading-digit asymptotic, the same cubic
search rectangle, and the same conclusion that Question 1.1 and Conjecture 3.8
are untouched. That shared core is proved exactly once in the merged article.
Where the two genuinely diverged — the explicit all-degree thresholds — both
results survive in full, as Theorems 7.3 and 7.4.

## Status and priority

This is an unrefereed research manuscript, not a proof-assistant formalization.
The mathematical target is explicitly the canonical decomposition and
Question 3.10 in arXiv v1; the definitions and numbering were checked against
rendered PDF pages, not only against search snippets or an experimental HTML
conversion. A current literature search did not locate a previous answer, but
global priority and present-day open status are not certified. The publisher's
final full text could not be inspected; its numbering or question wording is
not assumed to be unchanged. See `REFERENCES.md`, `STATUS.md` and Appendix C
of the article.

The primary finite counterexamples are completely specified and can be
checked by hand independently of that bibliographic limitation. No
third-party article PDFs or font files are included in this package.
