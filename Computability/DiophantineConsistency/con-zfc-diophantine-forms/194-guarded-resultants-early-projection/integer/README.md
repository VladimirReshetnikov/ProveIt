# An explicit quartic in 209 unrestricted integers

Read `report.pdf` or `PROOF.md` for the ordinary proof and exact scope.

| Endpoint | Variables | Quadratic rows | Degree | Terms | Height |
|---|---:|---:|---:|---:|---:|
| **Even-affine candidate** | **209** | **149** | **4** | **5,486** | **2^44** |
| Incoming Pell-growth parent | 210 | 150 | 4 | 5,282 | 2^40 |

One coordinate and one row are saved; support increases by 204 terms and
coefficient height by a factor of 16. This is a tradeoff, not dominance or a
global-minimum claim. The separate 212-variable control remains unchanged.

The sole construction change is `t=4h+2` in place of `t=16+4h_old²`, deleting
the private old root and row. The proof excludes `x=0` before assuming a
positive horizon, establishes `t≥2`, and supplies cofinal horizons with the
correct bit-20 no-carry binomial parity. The rejected odd-horizon escape
`t=-1, x=0, q=1` is preserved as a diagnostic control.

Full residuals and all collected coefficients are in `integer209/`.
Exact source and coordinate/frame certificates, the complete original210
archive, an independent checker and editable LaTeX are included. The
polynomial has an integer zero iff a finite ZFC refutation exists; neither
consistency nor nonsolvability is separately asserted.

Offline Python 3, standard library:

```sh
python3 -B verify.py
python3 -B -O verify.py
python3 -B verify.py --parent
python3 -B -O verify.py --parent
python3 -B build.py --out /tmp/rebuilt209
python3 -B verify_report.py
```

All checks are read-only except explicit receipt/output paths. Each replay
rebuilds from a fresh relocated package. The optional parent replay checks
the full original210 package and its inherited173 closure. New certificate
paths are relative. No network, root search or fresh proof-assistant build is
required or claimed. Optional document regeneration uses `build_tex.py`
(Pandoc), then `pdflatex report.tex` twice.
