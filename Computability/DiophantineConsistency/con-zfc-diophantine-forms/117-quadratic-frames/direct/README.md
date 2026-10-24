# Direct-C222 quartics from signed-output Pell frames

This portable packet supplies two explicit polynomials over unrestricted
integers, with complete quadratic residual lists, expanded coefficients,
integer projection inverses, ordinary proofs and independent source audits.

| Directory under variants/63 | Variables | Rows | Monomials | Degree | Height |
|---|---:|---:|---:|---:|---:|
| support32 |576|368|7,172|4|2,445,790,974,704|
| support16_affine2 |582|374|6,200|4|964,213|

For either directory, the equation is the sum of squares of every listed
quadratic residual in equation.json. polynomial.json is the same polynomial
fully expanded. All coefficients are literal integers. projection.json
contains every monic substitution and inverse. There are no variable-power
operations in the exported equations.

### JSON fields

`equation.json` has `variables` (an ordered list of coordinate metadata),
`residuals` (an ordered list of objects with `label` and `terms`), and
`metrics`. Its declared equation is the sum of the squared residuals.
`polynomial.json` has `variables` (the number of coordinates), `domain`,
`schema`, and `terms`. In either file, a term `[c, [i0, i1, ...]]` denotes
the integer coefficient `c` times the listed variables. Indices are
zero-based; repetitions encode powers. For example `[7, [0,0,3]]` means
`7*x0*x0*x3`, and `[-2, []]` is the constant `-2`.

`projection.json` records the parent and child bindings and every monic
elimination/restoration step. The independent verifier interprets every
step and checks both residual systems, including all integer inverses.

The theorem is existence equivalence with the pinned75-predicate direct-C222
source. Its prior ordinary refutation/Con(ZFC) calibration transfers
separately. The new source arithmetic is independent of K215, Jones
compression and Sun's integer reduction. The packet claims neither global
minimality nor a new checked internal-ZFC proof object.

## Reproduce offline

Python3 with its standard library suffices. Run these from this directory:

```sh
python3 -B independent_source_check.py
python3 -B check.py
python3 -B build.py --check
python3 -B -O independent_source_check.py
python3 -B -O check.py
```

The source checker imports no producer or optimizer. The projection checker
uses independently authored upstream verifiers and recollects every quartic
coefficient. The builder's check mode reconstructs the saved source, projections
and complete polynomials and compares the data exactly.

The theorem and proof are in the includable article section direct_section.tex.
PROOF.md maps its dependencies. INDEPENDENT_REVIEW.md supplies a separately
authored mathematical review. Normal/optimized exact source and polynomial
receipts are included. SOURCE_PINS.json records the immutable repository
snapshot and every copied source hash. The source folder contains all code
needed for the offline reproduction and the ordinary Pell/factorial lemmas
used in the proof. Original retained licenses/notices accompany those files.

The principal change replaces selected linear power-output terms in the
dominating Pell frame by their squares. A signed-residue argument then
recovers their true positive values, allowing sign predicates to be removed.
The ordinary proof explicitly reconstructs a fresh private Pell frame when
mapping back to the old source; it does not assume this map fixes the private
auxiliary coordinates.
