# Coordinated changes of integer coordinates

New completed fixed-polynomial points, compared with all six incoming archive
roots at ProveIt commit 08200eb10fde2db408c69dffd840d6920a569b1f:

| Integer unknowns | Exact degree | Residuals | Incoming predecessor degree |
|---:|---:|---:|---:|
|21|16|9|20|
|20|18|8|32|
|19|40|7|88|

The full proof is COORDINATE_PROOF.md; coordinate_section.tex is the editable
LaTeX section. The literal single equations are the sums of squares of the
listed residuals in equations/coordinate21_degree16.json,
equations/coordinate20_degree18.json, and equations/coordinate19_degree40.json.
All coordinates are unrestricted integers. All nonvariable symbols are the
six fixed numerals bound in COEFFICIENT_BINDING.json, or explicitly inlined
polynomial abbreviations. Actual coefficient bytes and their finite recipe
are included.

The new step keeps Y=a-E and k=eta+zeta as coordinates, reanchors the
transport at C=q-F-alpha, and then eliminates F,E,eta,V monically. A first
Pell-root translation lowers degree; a second auxiliary-root translation
preserves the improvement after I is removed. All new transformations are
integer-polynomial zero-set bijections. Their composition with the named
inherited ordinary calibration yields the desired consistency equivalence.

These are degree improvements at fixed variable counts. There is no global
minimality claim, no consistency decision, and no new end-to-end Lean/Rocq
or internally encoded object-ZFC certificate. The 25-variable octic and
other earlier packets included here are baseline reproductions, not new
contributions. PROOF.md is clearly labeled as their background derivation.

## Offline replay

Python 3.10+ and its standard library suffice:

    python3 build_family.py
    python3 build_coordinate_family.py
    python3 -O build_coordinate_family.py
    python3 check_coordinate_maps.py --directory . --output INDEPENDENT_REPLAY.json

The first command reauthenticates the immediate pinned sources, reconstructs
all coefficients, and regenerates the older baseline family. The second
regenerates the three new equations and checks their exact restoration maps,
the incoming elementary row bridge, every display row, degrees, nonzero
coefficient certificates, and liveness. The third confirms that the checks
do not disappear when Python assertions are disabled. Receipts are
VERIFICATION.json and COORDINATE_VERIFICATION.json.

The coefficient recipe is byte-authenticated before execution and reads only
the packaged machine and tile data. It does not run a Turing machine,
search for a refutation, use the network, or query consistency.

## Files and proof boundaries

- equations/: completely expanded residual lists and a compact baseline.
- coefficients/: six exact fixed-numeral gzip payloads.
- upstream/: immediate source34/64/68/70/71 proof/data dependencies.
- comparison/: all six incoming root texts, reviewed for overlap.
- incoming_joint25.json: immutable literal incoming zero-set baseline.
- SOURCE_PINS.json and INCOMING_PINS.json: exact provenance.
- polynomial.py: inherited standard-library exact arithmetic engine.
- build_family.py: baseline reproduction; build_coordinate_family.py: new work.
- coordinate_section.tex and COORDINATE_PROOF.md: the new universal argument.

Native compilation, Pell-rank classification, and the literal K215/refutation
calibration remain the explicitly identified ordinary source theorems. The
new polynomial maps need no positivity or nonzero assumptions and have no
division. Finite checks audit their literal algebra; they do not replace
the universal proofs or prove absence of zeros.

Inherited licenses and notices are retained under upstream/licenses/.
New material follows the repository's MIT No Attribution license.
