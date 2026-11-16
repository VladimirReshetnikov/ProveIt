# Conway criterion in iPRA

This packet gives a complete constructive proof of the **piecewise-linear Conway criterion** and an explicit route to an object-theory Lean formalization in ProveIt's intuitionistic primitive recursive arithmetic.

## Start here

- `paper/conway_criterion_ipra.pdf` — human-readable report.
- `paper/conway_criterion_ipra.tex` and `paper/sections/` — editable LaTeX.
- `lean/FORMALIZATION_PLAN.md` — dependency-ordered route to an actual `Prf PRAAx` theorem.
- `lean/ConwayCriterionBlueprint.lean` — executable host definitions and commented object-theory targets; no admitted facts.
- `code/conway_core.py` — exact rational reference kernel.
- `examples/zigzag_conway_tile_report.json` — worked certificate.
- `metadata/THEOREM_LEDGER.md` and `metadata/STATUS.md` — claim/status boundaries.

## Main result

For a rational PL disk whose oriented boundary is split into paths `a,b,c,d,e,f` satisfying Conway's translated-pair and four half-turn equations, define

```text
t = E-A = D-B,
u = E+F-B-C,
H_e(x) = E+F-x.
```

Then

```text
T + m t + n u,
H_e(T) + m t + n u                         (m,n in Z)
```

is a periodic tiling of the plane.  The proof projects the two representatives to the torus `R²/(Zt+Zu)`.  Their boundary cancels exactly.  A finite common subdivision turns them into a nonnegative 2-cycle, so all face multiplicities are equal.  The exact identity

```text
det(t,u) = 2 area(T)
```

forces that multiplicity to be one.  This closes the usual informal gap at tiling vertices without invoking classical covering-space theory.

## Reproduce

```bash
(cd code && python3 -m unittest -v test_conway_core.py)
python3 code/conway_core.py examples/zigzag_conway_tile.json \
  --output examples/zigzag_conway_tile_report.json
python3 figures/make_figures.py
bash build.sh
```

The Python core uses the standard library.  Figure generation uses Matplotlib.  PDF generation uses a conventional TeX Live installation.

## Scope

The exact iPRA statement is for number-coded finite PL data and certificates.  It is the natural first-order arithmetic form of the criterion for polygons, polyforms and finitely described curved approximations.  The packet does not pretend that first-order iPRA quantifies directly over arbitrary subsets of the Euclidean plane or arbitrary continuous functions.

The supplied Lean file is an uncompiled blueprint, not a completed formal proof.  See `metadata/STATUS.md`.
