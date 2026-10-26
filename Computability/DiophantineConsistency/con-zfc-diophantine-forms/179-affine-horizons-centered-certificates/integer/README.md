# Affine pooled quartics in 215 unrestricted integers

Start with `report.pdf` (12 pages, including all sparse residuals).

The recommended literal equation is `integer215_sparse/equation.json`, the sum
of squares of all **152 quadratic residuals in 215 independent integers**.
Every collected coefficient is in `expanded_polynomial.json`.

| Endpoint | Variables | Rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| Sparse principal | 215 | 152 | 4 | 14,578 | 16,866 |
| Low-height alternative | 215 | 152 | 4 | 34,700 | 4,512 |

The sparse equation improves the prior217-variable sparse point in dimension,
rows and support at unchanged height, and the incoming216-variable point in
all four measures. The low-height alternative trades additional support for
smaller coefficients. Neither is claimed globally minimal.

`PROOF.md` gives both directions of the ordinary equivalence with finite ZFC
refutation, hence nonsolvability iff Con(ZFC). It does not prove consistency.
The new compatibility estimate combines weak affine atom bounds with a
fourfold Pell frame, enabling the credited affine-horizon method inside the
credited pooled-power construction. One further exact shared-consumer
contraction is explicitly credited to source158.

The package supplies full residuals/expansions, an editable LaTeX section,
source closure, all maps, frozen reconstruction, and an independent checker.
Python 3, standard library, offline:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --parent
python3 -B build.py --out /tmp/rebuilt215
```

Verification is read-only unless `--receipt` is explicitly supplied. Every
rebuild runs from a fresh relocated copy of the complete package, so execution
paths cannot silently enter deterministic certificates. No remote
write, repository commit, proof-assistant recompile, or zero search is claimed.
