# Discrete Initial Groups and Omnific Normalization

**Sign-tree surgery, a sharp image classification, and an Ehrlich–Kaplan question**  
AI-assisted research draft prepared for the Surreal project  
23 September 2026

## Status

The delivery describes a 24-page research article with full proposed proofs of an
affirmative answer to Ehrlich and Kaplan's discrete-initial-subgroup question,
together with structural refinements and reproducible finite regression checks.
It is an unrefereed manuscript, not an independently certified resolution or a
claim of established priority. The mathematical argument and the novelty claims
require independent review. No new Lean formalization is claimed.

Placement `c6359e4` retains the source as `article.tex`, with verification
code under `code/` and its recorded output under `data/`. No maintained PDF
was placed. The reported page count and visual checks below describe the
delivery, not a new repository build. The formalization ledger indexes the
26 standard results and separately records three custom main theorems, all
pending.

The question is Question 2 in Section 9, printed page 18, of arXiv:1512.04001v1.
The crucial imported result is the concrete sufficiency direction of Theorem 1
of that preprint: its proof establishes initiality of the specified canonical
normal-form image, not merely the existence of an unspecified initial copy.
The article identifies this dependency explicitly.

## Main contents

- **Explicit omnific normalization.** For an initial additive subgroup with least
  positive element `2^(-n) omega^(-alpha)`, an explicit order-preserving additive
  isomorphism gives an initial subgroup of the omnific integers. It changes the
  exponent sign tree and rescales only the bottom coefficient.
- **Exact range and inverse.** The images at a prescribed least-positive scale
  are exactly the initial omnific subgroups containing the stated dyadic-spine
  group. The article also gives extremal realizations, a sharp cardinality bound,
  and an admissible-scale criterion.
- **Cyclic quotient and converse.** The quotient by the least positive cyclic
  subgroup has an explicit initial surreal realization. Conversely, adjoining
  a lexicographically subordinate copy of the integers is realized by a
  sign-prefix operation. A relative splitting criterion follows.
- **Strong sums and surcomplex modules.** The normal-form maps preserve support
  order types, leading truncations, and set-indexed strong summability. A
  coordinatewise extension is Gaussian-linear on rectangular surcomplex
  modules. Multiplicativity, norm preservation, and preservation of the entire
  ambient simplicity relation are not asserted.

The paper contains finite and transfinite examples, counterexamples to tempting
but invalid shortcuts, a compact proof appendix, and a proof-review checklist.

## Files

| File | Purpose |
|---|---|
| `article.tex` | Standalone LaTeX source; bibliography is embedded. |
| `code/verify.py` | Exact finite regression checks; Python standard library only. |
| `data/verification_report.json` | Delivered PASS result, scope, and assertion counts. |
| `source_audit.md` | Primary sources, repository provenance, and review limits. |
| `code/build.sh` | Delivered build script; expects the original source name beside it and does not build this placed layout. |

## Reproduce the tests

Requires Python 3.10 or later. No external Python packages or network access are
needed.

```sh
python3 code/verify.py --output /tmp/omnific-normalization-verification.json
```

The recorded run passed **450,862 assertions**. It covers finite sign words
through length seven, all **677** prefix-closed sign trees through depth three,
finite inverse/spine conditions, and 1,500 randomized pairs of finite rational
normal forms with fixed seed 20260923. The empty tree is included in the 677;
there are 676 nonempty source trees.

These are regression checks for the formulas, not a verification of transfinite
ordinal concatenation, arbitrary Hahn sums, the imported initiality theorem, or
the mathematical manuscript as a whole. The JSON report records these limits.

## Rebuild the article

A TeX installation with pdfLaTeX and the packages named in the preamble is
required. In particular, the article uses `newtxtext`, `newtxmath`, `microtype`,
`tikz`, `tcolorbox`, `hyperref`, and `cleveref`, in addition to common AMS and
layout packages. No font files are included in this package.

From this report directory, compile the placed source into a scratch directory:

```sh
mkdir -p /tmp/omnific-normalization-build
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/omnific-normalization-build article.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/omnific-normalization-build article.tex
pdflatex -interaction=nonstopmode -halt-on-error -output-directory=/tmp/omnific-normalization-build article.tex
```

The delivery reports a successful PDF build with resolved cross-references,
no overfull boxes and visual review of all 24 pages. This placement has not
independently repeated that build. Compilation and rendering establish
document integrity, not mathematical correctness.

## Relationship to the repository

The article was prepared after a targeted read of the Surreal repository's
README, formalization ledger, directory/tree metadata, and targeted searches.
It does not claim a full repository audit and does not rely on unreviewed
repository manuscripts. The repository was not modified, and no repository Lean
build was performed for this package. Exact read identifiers and the distinction
between those reads and a later observed commit are recorded in `source_audit.md`.
