# Verification record

Delivery date: 15 November 2026.

## Written mathematics

The 42-page report contains the human proof and the finite arithmetic
contracts. The functional-equation foundation is reused from the unchanged
upstream archive in `dependencies/`. Its original, incomplete Lean status
is preserved. The source manifest pins the inspected ProveIt revision and
records the hashes of the source material used.

The mathematical arguments were reviewed for the distinction between
quantifier-free induction and unrestricted induction, uniform versus
fixed-degree polynomial procedures, positive contour clearance, the
absence of unbounded search, and the continuous choice of gamma argument.
This review is human-level mathematical review, not formal verification.

## Executed computations

Environment: Python 3.12.14, standard library only for both included Python
programs.

Executed from the archive root:

```sh
python3 code/rational_zeta.py
python3 code/good_height_bounds.py > verification/bounds_examples.json
```

Both commands exited successfully. The first regenerated
`verification/simple_zero.json` and passed the exact rational Rouché,
derivative, and contraction comparisons. Its displayed decimal summaries
include:

| Quantity | Displayed value |
| --- | --- |
| Center residual upper bound | 0.000000000000005638247487151467 |
| Rouché left side | 0.000000004096005638252887 |
| Rouché right side | 0.000000783296511867110774 |
| Derivative lower bound | 0.77715251186710537424 |
| Contraction upper bound | 0.00784377296071471977 |

The exact fractions, rather than these rounded displays, are used in the
comparisons. The Euler–Maclaurin remainder includes the factor of two
needed to convert its Euclidean error estimate into an L1 ball error.
The computation uses no floating-point special-function library.

The second command calculated the theoretical cutoff sizes for the sample
heights in its output. It did **not** execute the general regular-height
search, construct its enormous contours, or enumerate all zeros below
those heights. Termination and uniform correctness of those procedures
are subjects of the written proof.

## PDF build and inspection

The report was compiled with pdfTeX 1.40.26 / LaTeX using the supplied
source. The final compilation produced 42 US-letter pages with no
undefined references, LaTeX warnings, or overfull/underfull boxes.
All pages were rendered with Poppler and inspected in contact sheets;
the central counting statement and worked-certificate pages were also
inspected individually. The final bibliography and long source paths fit
within the page margins.

This environment required a scratch-local TeX format and font-map setup
because the installed TeX file index was incomplete. This affected the
local runtime setup, not the report source. The supplied `build.sh` uses
an ordinary working TeX Live installation and makes three LaTeX passes.

## Lean status

No Lean executable was available in this environment. The new
`lean/ObjectTargets.lean` file was **not compiled**. It is an interface and
roadmap based on the inspected repository APIs. It contains no `sorry`
and adds no analytic axiom, but no instance of its `Completed` structure
is supplied. No new internal derivation of a zeta theorem is claimed to
have been kernel-checked.

The intended endpoint remains an actual term of `Prf PRAAx [] phi` for
the specified, correctly implemented arithmetic programs, with transfer
through the existing `pra_iff_native` theorem. A proof of a different,
constant-one checker would not meet these contracts.

## Archive integrity

The included upstream source files and dependency ZIP were checked
against their recorded SHA-256 hashes and Git blob identifiers. The
delivery ZIP was checked for readable entries and the presence of the
PDF, all TeX sources, code, Lean outline, provenance, and verification
outputs. `SHA256SUMS` records the individual delivered files; it excludes
itself. Build intermediates and rendered preview images are not included.
