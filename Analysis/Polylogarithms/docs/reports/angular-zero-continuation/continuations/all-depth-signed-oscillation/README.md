# Signed-Kernel Oscillation at Every Depth

**Minimal Pick Compensation, Zero Geometry, and Certified Polylogarithmic Identities**

Research continuation for Vladimir Reshetnikov's ProveIt project, October 10, 2026.

## Main results

For strict single-variable multiple polylogarithms of depth d, with the first
d-1 indices positive integers and the final index an arbitrary positive real:

* An explicit two-operator L1 construction has exactly d-1 simple sign changes,
  with interlacing under outer-index raising and strict depth raising.
* Its zero polynomial produces a finite positive Stieltjes measure. The
  compensator has minimal degree d-1 and is unique after normalization.
* The principal function has no nonzero zero on C minus [1,infinity).
* Every upper semicircle of radius at most one has exactly d-1 simple
  imaginary-part zeros. Every angular branch is strictly decreasing in radius.
* The same structure holds for positive terminal mixtures and a shifted-terminal
  Lerch family. The article gives expansions and an explicit infinite family of
  positive logarithmic integral identities.

The article contains ordinary analytic proofs. The Python replay is finite exact
arithmetic evidence for their computational interfaces, not a proof-assistant
formalization. S6, S8, unrestricted fractional leading indices, arithmetic period
independence, and the existing normalized-radius conjecture are not claimed solved.
No universal literature-priority claim is made.

## Files

`article.pdf` is the compiled article. `article.tex`, `sections/*.tex`, and
`references.tex` are its complete editable source. `CLAIM_STATUS.md` and `AUDIT.md`
record scope, proof status, and review findings.

`code/exact_evaluator.py` evaluates integer-index examples using exact rational
centered moments and a proved geometric remainder. It has no third-party dependency.
`code/verify.py` replays the frozen certificates and runs independent exact tests.
`data/gaussian_enclosures.json` contains eight complex Gaussian enclosures, each with
error radius below 1e-81. `data/angular_brackets.json` contains 24 certified angular
brackets at radius 1/2, each of t-width at most 1e-12 for theta=2 atan(t).
`data/verification_report.json` records 5,713 passing finite check groups.

`integration/all_depth_synopsis.tex` is an additive manuscript synopsis.
`integration/notation_corrections.patch` proposes two notation-only fixes in the
existing Hurwitz transport proof. `INTEGRATION.md` explains placement and safe checks.
`data/source_provenance.json` pins the reviewed repository snapshot.
`SHA256SUMS` covers delivered files other than itself.

## Reproduce

From this directory:

```sh
python -m pip install -r requirements.txt
python code/verify.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The default replay uses frozen brackets and exact arithmetic, not a numerical root
search. Optional regeneration uses floating point only to propose brackets, then
accepts them only after rational endpoint-sign certification:

```sh
python code/verify.py --regenerate
python code/exact_evaluator.py 2 1 2 --terms 240
```

The evaluator's exact implementation accepts positive integer indices only.
The article's arbitrary positive real final index is a proved analytic extension,
not an undocumented rational-arithmetic feature.

## Integration and source review

Reviewed repository reference:
`3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f`.
The review was targeted at the manuscript's signed-kernel, real-order, positive-kernel,
subcritical, local-radius, and research-status sections; it was not a full audit of
the entire repository. The two proposed transport-proof replacements are `q=n` to
`x=n`, and boundedness of `h` to boundedness of `q`. They do not change its theorem.

Nothing has been pushed, uploaded, or applied to the remote repository.

## Tested environment

Python 3.13.5, SymPy 1.14.0, mpmath 1.3.0, NumPy 2.3.5; pdfLaTeX through latexmk.
