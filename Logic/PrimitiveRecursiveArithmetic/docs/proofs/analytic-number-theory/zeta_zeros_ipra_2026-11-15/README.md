# Zeta zero distribution in intuitionistic primitive recursive arithmetic

Prepared for Vladimir Reshetnikov, 15 November 2026.

Start with **zeta_zeros_ipra.pdf**. Its complete source is
**zeta_zeros_ipra.tex** and the files in **sections/**.

## Mathematical contents

The report gives quantitative constructive proofs of Euler-region
nonvanishing; positive clearance on the one-line and a narrow neighborhood;
the simple trivial zeros and their derivative formula; critical-strip
localization; conjugation and reflection symmetry; an explicit primitive
recursive regular-height constructor; the Riemann--von Mangoldt estimate

    |N(U) - U/(2*pi)*log(U/(2*pi)) + U/(2*pi)| <= 8*log(U+4) + 40;

unbounded zero counts with bounded witnesses; logarithmic local counts and
multiplicity bounds; growing-window mean density; and effective reciprocal
zero-sum tails. A uniform finite algebraic root engine handles rational
polynomials of varying degree, instead of assuming a fixed-degree FTA
schema suffices. Positive contour counts have a finite winding formulation;
a bounded subdivision construction extracts a uniform sequence of pairwise
apart primitive recursive names for nontrivial zeros.

The archive also supplies an exact-rational certificate for one simple
critical-line zero in the disk centered at
`1/2 + 14.1347251417347 i` of radius `10^-6`. This is not a claim that the
zero is the lowest positive zero.

## Proof and verification status

- **Human mathematics:** full written quantitative arguments and a finite
  arithmetic interpretation are in the report. The functional-equation
  foundation is reused from the included upstream human proof.
- **Executed arithmetic:** `code/rational_zeta.py` recomputes exact-rational
  Euler--Maclaurin enclosures and verifies the Rouché, simplicity, and
  contraction inequalities. No floating-point special-function library is
  used in that computation.
- **Theoretical resource bounds:** `code/good_height_bounds.py` calculates
  exact bound sizes. It does not execute the astronomical general contour
  search.
- **Lean:** `lean/ObjectTargets.lean` is an uncompiled interface and roadmap.
  It adds no analytic axiom and contains no `sorry`, but does not construct
  the internal analytic proofs. It must not be represented as a completed
  Lean formalization. The intended endpoint is `Prf PRAAx [] phi`, followed
  by the repository theorem `pra_iff_native`.

The report does not prove the Riemann hypothesis, Hardy's critical-line
infinitude theorem, a critical-line proportion, or a sharp logarithmic
zero-free region.

## Reproduce

Python 3.12 or a compatible later Python, standard library only:

```sh
python3 code/rational_zeta.py
python3 code/good_height_bounds.py > verification/bounds_examples.json
```

The first command writes `verification/simple_zero.json`. The second only
calculates resource bounds. Run `./build.sh` to execute both computations and
compile the PDF using a normal TeX Live installation.

## Repository provenance

Inspected repository: `VladimirReshetnikov/ProveIt`, commit
`b5a3ad037723c44d69a3d5b28a950c554327a989`.

`sources/source_manifest.json` records pinned URLs and source hashes. The
copied source files are evidence of the APIs inspected, not a self-contained
copy of all their Lean dependencies. The original functional-equation ZIP
is preserved under `dependencies/`. Its own incomplete Lean status is
retained. Other drafts listed in the manifest were inspected for scope but
are not mathematical prerequisites of the main argument and are not
redistributed in this archive.

No GitHub write was made. The archive can be integrated into ProveIt as a
research package; it has no claim to be an already merged repository change.
