# Validation record

Validation date: 2026-11-15.

## Paper build

Command:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error goldbach_euler_ipra.tex
```

Result: success. The resulting PDF has 14 US-letter pages, embedded fonts,
bookmarks, and no encryption. The final LaTeX log contains no overfull boxes,
underfull boxes, or package warnings.

The PDF was rendered at 180 dpi with the repository PDF validation workflow.
All 14 rendered pages were visually inspected; no clipped text, overlap,
missing glyphs, or malformed equations were observed.

## Exact finite checks

Command:

```bash
python checks/finite_check.py --output-dir checks --canonical-limit 3000
```

Result: success. The generated report ends with `All exact checks passed.`
The checks use Python standard-library `fractions.Fraction`; displayed decimal
values are only summaries of exact rational computations.

## Lean status

No Lean executable was available in the build environment. Therefore:

- `lean/GoldbachEulerOutline.lean` is explicitly an uncompiled outline and
  contains `sorry` obligations.
- `lean/ConciseIPRABridge.lean` was checked textually against the pinned
  ProveIt declarations `PRAAx`, `NFm.ofPRA`, `NPrf`, and `pra_iff_native`, but
  was not locally compiled.

Nothing in this package is described as a completed Lean formalization.
