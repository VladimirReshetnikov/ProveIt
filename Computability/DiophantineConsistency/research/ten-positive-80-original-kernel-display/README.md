# Ten-variable original-kernel decimal display

`equation.tex` and `equation.pdf` show the separately constructed
[original-kernel 80-row candidate](../ten-positive-80-original-kernel-variant/README.md).
The ten strictly positive unknowns have distinct names `a` through `j`;
registers `r01` through `r80` are abbreviations, not extra unknowns. The
equation uses ordinary integer arithmetic, including signed intermediate
values. The four fixed integers are specified by formulas and a decimal list
of 943 selectors, so the display is self-contained. All written numerals use
base 10. The 80-operation count is for the given positive-domain row graph;
it excludes fixed-constant construction and the ten shifts used to express
positive variables as unrestricted natural variables. Exact degree 750 has a
separately reviewed external modular certificate in the candidate packet.

The [fixed symbolic Lean endpoint](../ten-positive-80-symbolic-ipra-client-prototype/FIXED.md)
asserts the corresponding no-zero equivalences are derivable in standard and
equality-only iPRA for the once-shifted Lean graph. The graph/TeX/PDF and
symbolic-kernel/payload correspondences in this display are **external
checks**, not Lean file or PDF semantics theorems. The fixed Lean endpoint's
full historical source/object, package and dynamic dependency ancestry also
remains inherited. This is the original-kernel variant: it is not the
different direct-BFS coefficient in `ten-positive-unshift-t-finite`.

Run `python3 -I -S -B generate.py --output build01` from this directory,
using a fresh output name. Two separate builds produced byte-identical TeX
and PDFs. The retained `check_display.py` verifies all 80 extracted PDF rows,
the 41 slots and 943 decimal selectors, full fixed coefficient payloads,
the constant pages against a separately reviewed reference, and word bounds
on all four PDF pages. `observations/check01/` records its successful output
and hashes. The first two pages were also visually inspected. These checks
are not an independent Lean replay or proof of PDF semantics.

TeX SHA-256: `a692c2c5eb3babd6677b7a26408877c5f5d4d27fb5d2cb502dcdd0614645db01`.
PDF SHA-256: `e6cba9c0124eeb35f0013ccde85753a2add8090ed390296f34227ffcfb544017`.
