# A countable genetic cut across the finite–infinite gap

Research note prepared for Vladimir Reshetnikov — 20 September 2026.

## Main result

With N the ordinary finite natural numbers, put

    q(t) = t / (1 + t^2)
    T(x) = { q(n-x) : n in N | }
    B(x) = 1 - T(x).

Braces are Conway cuts: they select the simplest surreal strictly above all
left options and below all right options. They are not supremum notation.

The paper proves that B is the indicator of the positive infinite surreals,
is genetic under the set-sized option constructors in the cited sources,
and has pointwise derivative zero everywhere. Consequently x and x-B(x)
are genetic primitives of 1 which agree at every real input but do not
differ by a constant. The latter is also an increasing bijection.

The sublevel class {x : 0 < x < omega, B(x) <= 1/2} has no surreal supremum.
It is nonempty and bounded, so neither end gap supplies its supremum.

The targets are Conjecture 53 of Rubinstein-Salzedo–Swaminathan (2014) and
Chapter 8, Conjecture 3 of Berenbeim (2022). The original paper ALREADY prints
the piecewise primitive x-B(x). The additional observation here is its
explicit genetic realization and the deductions from that realization.

## Contents

- `article.pdf`, `article.tex`: 16-page article, complete proofs, general
  set-generated gap indicators, order automorphisms, ordinal-indexed
  independent families, topology and hyperreal distinctions, definition audit.
- `short_proof.pdf`, `short_proof.tex`: two-page proof of the core results.
- `code/verify.py`: exact finite computational checks; Python standard library.
- `results/verification.json`: actual run output (7,248 checks on 84 rational
  functions, plus finite cut and scale tests, all passing).
- `results/proof_status.json`: mathematical and validation status.
- `results/pdf_preflight.json`: structural and text-bound checks of the PDFs.
- `source_manifest.json`: primary sources, checked locations and search scope.
- `build.sh`, `build.ps1`: POSIX and PowerShell reproduction scripts.

## Reproduce the computations

Python 3.9 or later, with no third-party modules:

    python code/verify.py

On Windows with the Python launcher, `py -3 code/verify.py` works as well.
The default output is `results/verification.json`, relative to the script's
project directory. Run `python code/verify.py --help` for the output option.
The bundled run used Python 3.13.5. The `python_version` field naturally
changes on other Python versions.

The program works in the exact ordered field Q(t), where t is positive
infinite, and also checks finite Conway cuts over rational option values.
It does NOT implement all surreal numbers, prove an infinitary quantifier,
check the genetic-function definitions, or replace the proofs in the paper.
In particular, no finite truncation of the countable cut establishes the
zero-derivative theorem: every finite truncation has an actual jump point.

## Rebuild the PDFs and rerun the tests

Use a TeX distribution with pdfLaTeX and the packages declared in the TeX
preambles. `newpxtext`/`newpxmath` supply the document's Palatino-style type.
No font files or copies of the cited papers are included.

POSIX shell:

    ./build.sh

PowerShell:

    ./build.ps1

The scripts use `latexmk` when available, and otherwise run `pdflatex` three
times. They do not install software, download dependencies, or modify the
system configuration. Both PDFs are built from the supplied source; no
bibliography processor is needed. Rebuilding PDFs may change metadata and
file hashes even when their mathematical contents are unchanged.

## Status and scope

The supplied arguments prove the stated counterexamples under the published
set-sized option conventions, including the usual treatment of option
expressions that do not use input options. The strengthened global
cofinality condition in the dissertation is checked explicitly.

This is not a claim about a narrower class allowing only finitely many
option expressions, nor about an arbitrarily chosen derivation on the
surreal field. The derivative is the pointwise order-field derivative of a
function, with all positive surreal epsilon and delta allowed.

No later resolution was located in the recorded searches, but the search
was not exhaustive and establishes neither priority nor absence of
unpublished work. The work has not been independently refereed or checked
in a proof assistant. Computational checks are finite consistency tests;
mathematical validation rests on the displayed proofs and definition audit.
