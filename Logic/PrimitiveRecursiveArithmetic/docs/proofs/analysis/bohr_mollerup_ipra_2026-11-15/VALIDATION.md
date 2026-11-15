# Validation record

Date: 2026-11-15

## Mathematical cross-checks

- The standard normalization/recurrence/log-convexity statement was checked
  against DLMF and the current Mathlib Bohr–Mollerup module.
- The indexing of the Euler brackets was cross-checked against the standard
  squeeze.
- The exact integer-power predicates behind monotonicity were exhaustively
  tested for all reduced/nonreduced fractions `a/b` with `1 ≤ a ≤ b ≤ 15` and
  `1 ≤ n < 20`.
- The global Euler-approximant factorization and the displayed `C_m/n` error
  bound were independently numerically checked on a grid of strip parameters.
  This numerical check is supplementary; the report gives the finite proof.

## Executable artifacts

Commands run successfully:

```text
python3 -m py_compile code/bm_bounds.py code/test_bm_bounds.py
python3 code/test_bm_bounds.py
python3 code/bm_bounds.py --verify sample_certificate_half.json
```

The certificate verifier uses exact integer and `Fraction` arithmetic.

## PDF

The LaTeX source was compiled with `latexmk`/`pdflatex`. The resulting PDF has
17 pages. It was rendered to PNG at 150 DPI with the PDF skill renderer and
inspected as a contact sheet and at full-page resolution for representative
pages (title/abstract, proof tables, Lean roadmap, and bibliography). No
clipping or unresolved references were observed.

## Lean status

No `lean` or `lake` executable was present in the build environment. Therefore
`lean/BohrMollerupOutline.lean` is explicitly delivered as an uncompiled
scaffold with `sorry` milestones, not as a verified formal proof. The report
and `lean/LEAN_ROADMAP.md` specify the path to a completed object-level proof
using the existing ProveIt `ConciseIPRA.PR` and `BiInterpretation` files.
