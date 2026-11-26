CYCLOTOMIC VALUATIONS IN GRAPH TOWERS AND PROGRESSION-FREE SETS OVER FINITE RINGS
Research report, 25 November 2026

Open report.pdf for the main proofs. Its source is report.tex and the TeX
files alongside it. The nine-row table refers to arXiv:2606.03579v1.

The separate note supplement/wild-cubic.pdf determines the finite-tolerance
obstruction at every primitive 3-power conductor h>=2 over Q_3(cube root of 3).
Here h is the exponent in the order 3^h. Its source is wild-cubic.tex.

Build the main article from the top directory of this archive with
  latexmk -pdf report.tex
Build the supplement from its own directory with
  latexmk -pdf wild-cubic.tex
Two or three runs of pdflatex on each entry file also suffice.

All checks use Python 3 and its standard library. From the top directory run
  python3 verification/check_graphs.py
  python3 verification/check_kataoka.py
  python3 verification/check_dv3.py
  python3 verification/check_odd_rows.py
  python3 verification/check_products.py
  python3 supplement/check_wild_cubic.py
  python3 supplement/check_wild_tower.py

The matching *_results.txt files record the outputs. These checks use exact
integers or rational numbers for their assertions. In the product-ring
transcript the last two displayed decimals are rounded for readability.

verification/source-audit.txt lists pinned Lean sources with line numbers
and SHA-256 file digests. verification/incoming-inventory.txt lists the 41
comparison ZIPs by Git blob SHA-1. The two articles give mathematical
proofs. The formal Lean replay results discussed in the main article are
those reported by the upstream release. The included scripts check numerical
and finite parts of the new arguments. SHA256SUMS covers the archive contents
apart from the manifest itself.
