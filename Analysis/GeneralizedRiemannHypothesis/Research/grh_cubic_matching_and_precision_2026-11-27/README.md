# Exact Cubic Euler-Factor Matching and Optimal Unequal-Precision Recovery

Research report prepared with ChatGPT on 27 November 2026.

Start with **report.pdf**. Its complete LaTeX source is **report.tex**, with
chapters in `papers/`, a shared `preamble.tex`, and `references.bib`.

## Results

1. An exact formula, for every character-group rank and packet size, for
   the least density of primes distinguishing two distinct products of
   cubic Dirichlet L-functions. Every extremizing pair is classified.
   The result remains sharp when every factor is nonprincipal.
2. Sharp asymptotic erasure and corruption thresholds. Using the supplied
   Dirichlet GRH, finite distinguishing-prime and uniform extremal
   prime-counting estimates.
3. An exact observation kernel for bivariate formal series evaluated along
   branches with arbitrary unequal truncation lengths. It gives exact
   total-degree jet recovery, optimal recording budgets, target-specific
   error/erasure distance, and a contact-tree pruning algorithm.

The main cubic density theorem and all branch theorems are unconditional.
Only the explicitly marked analytic consequences use Dirichlet GRH.

These are mathematical proofs with exact finite checks, **not newly
Lean-certified theorems**. No fresh build or kernel replay of the vendor
package was run here. The report distinguishes the source audit from
external verification reports.

The exact results are new relative to the supplied collection and were not
located in targeted primary-literature searches. This is not a worldwide
priority certification. Established coding theorems, P-orderings, weighted
greedy methods, and ordinary coding-distance arguments are attributed.

## Build

Requirements: Python 3.10 or later, NumPy, Matplotlib, and a standard TeX
installation with `pdflatex`, BibTeX, `latexmk`, Latin Modern, AMS packages,
`microtype`, `booktabs`, `tabularx`, `enumitem`, `fancyhdr`, `xurl`,
`hyperref`, and `bookmark`.

```sh
python3 -m pip install -r requirements.txt
make pdf
make verify
```

The delivered PDF is already compiled, and all verification JSON files are
included. Running the checks replaces their corresponding outputs;
runtime measurements and library versions can differ between machines.
Exact mathematical outcomes should agree. `make figures` regenerates the
two PDF/PNG illustrations from the exact formulas and examples.

## Verification artifacts

| File | Purpose |
| --- | --- |
| `code/cubic_verify.py` | Exhaustive comparison of 17,735,976 unordered packet pairs; local valuation, extremizer, construction, norm, and explicit modulus-1729 checks |
| `code/cubic_independent_enumeration.py` | Separate exact implementation covering 1,036,722 unordered pairs |
| `code/verify_unequal_branches.py` | 747 branch/precision profiles, 2,996 direct rank comparisons, 2,996 subset checks, and sharp examples |
| `results/*.json` | Actual machine-readable outputs and environment |
| `provenance/math_review_*.md` | Independent mathematical proof reviews, including corrections |
| `code/audit_sources.py` | Reproducible source identity, imports, and lexical audit; does not invoke Lean |
| `provenance/source_static_audit.json` | Complete 803-module import closure and audit results |
| `provenance/upstream_tree_identity.json` | Independently obtained upstream tree identity |
| `provenance/source_manifest.json` | SHA-256 hashes and Git identities of the analyzed source inputs |
| `provenance/literature_search.md` | Search scope, primary sources, and limits of the novelty claim |

The source repository and external papers are not bundled. Their pinned
links are in the report and provenance files. All supplied code is readable
and self-contained apart from the listed numerical/plotting packages.

## Pinned source

- ProveIt: `2a9f8e3ee74a1824d57546f0b1b4f1cef5df93d6`
- Upstream `lsernau/grh-lean`: `72fead102f663d5c7a407964a13dc0cf9d977207`
- Matching `grh` Git tree: `2e133df63d7f4da6b3059c4195324f8e9187ba73`
- Lean: `v4.35.0`
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`

Given a separately obtained ProveIt checkout at the pinned revision:

```sh
make source-audit SOURCE=/absolute/path/to/ProveIt
```

`source-audit` reads that checkout and writes only its local JSON output.
It checks all 818 vendor working files against their Git blob identities.
The optional `--upstream-checkout` argument to `audit_sources.py` checks an
independent upstream checkout as well. The upstream API identity observed
in this session is preserved separately.

## Deliberate scope limits

- The cubic theorem determines the exact minimum and all equality cases,
  not every nonextremal density or every odd prime exponent.
- Branch coefficients are in a field. Mixed rings O/pi^r for r>1 and a
  fast error-location decoder are not solved here.
- The tree algorithm computes exact distance and worst deletion sets;
  its operation bound is pseudopolynomial in the maximum precision.
- No `.lean` file with unproved placeholders is supplied as a certificate.

`SHA256SUMS` identifies the bytes of the delivered package. Third-party
source code and papers retain their original authorship and licenses;
the archive contains links and analysis rather than redistributing them.
