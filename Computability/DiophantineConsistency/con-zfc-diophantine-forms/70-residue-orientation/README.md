# Residue orientation and root transfer

**Explicit improvements to Diophantine consistency equations**, prepared
for ProveIt on 23 October 2026.

Start with `report.pdf` for the complete mathematical account. Its source
is `report.tex`, with component sections in `integer/section.tex`,
`positive/section.tex`, and `eleven/section.tex`.

## Results

Each polynomial below has a zero in its stated domain if and only if there
is a finite syntactic ZFC refutation, by the ordinary mathematical proofs
in this release and their explicitly identified inherited theorems. Thus
ZFC proves that its lack of solutions is equivalent to Con(ZFC).

| Literal equation | Domain | Variables | Exact degree | Binary operations |
|---|---|---:|---:|---:|
| `integer/quartic40_direct.json` | All integers | 40 | 4 | Not optimized |
| `integer/sextic34.json` | All integers | 34 | 6 | Not optimized |
| `integer/octic29.json` | All integers | 29 | 8 | Not optimized |
| `eleven/p11_positive_degree325.json` | Strictly positive integers | 11 | 325 | 113 |
| `positive/p12_positive_degree84.json` | Strictly positive integers | 12 | 84 | 103 |
| `positive/p13_positive_degree30.json` | Strictly positive integers | 13 | 30 | 94 |

The recommended quartic is the sum of squares of its 25 listed quadratic
residuals. It replaces the parent coordinate by `X_old = 3*X3 - 1` and
deletes a square positivity witness. A new signed Pell argument proves
that the residue condition selects the correct power-of-two branch.

The alternate `integer/quartic40.json` restricts the existing J and scale
coordinates instead. This preserves a monic X definition, enabling exact
polynomial eliminations to the sextic and octic. Both quartics are proved.
The direct quartic has 393 expanded symbolic monomials, versus 388 in its
41-variable parent; the alternate parent has 614. Variable count improves,
but expanded expression size does not.

The twelve-positive equation transfers a strong Pell root into an
existing positive transport gap. A two-root norm eliminates the root,
with an explicit integrality argument and a strict positivity estimate
for the inverse map. Its three residuals have degrees 42, 13, and 37;
their sum of squares has exact degree 84. The circuit uses 60
multiplications, 27 additions, and 16 subtractions, with large fixed
coefficients counted as input leaves. Registers are polynomial
abbreviations, never extra quantified variables.

The eleven-positive extension transfers the first, strong, and auxiliary
Pell roots into one transport carrier while retaining the adaptive main
Pell equation separately. A stronger divisibility choice makes the
auxiliary root's denominator coprime to the transport denominator and
forces the recovered rational root to be an integer. Its two residuals
have degrees 312 and 13; a modulo-four unit-product argument gives one
equation of degree 325, evaluated in 67 multiplications, 29 additions,
and 17 subtractions. Norms, positive majorants, and unit-product
finalizers are inherited techniques; the new claim is their stated
composition with normalization and denominator recovery.

## Comparison and claims

The reference snapshot is
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` of
<https://github.com/VladimirReshetnikov/ProveIt>.

* Integer counts at degrees 4, 6, and 8 improve from 41, 35, and 30
  to 40, 34, and 29, respectively (packages 64 and 62).
* The eleven-positive point improves from degree 954 / 113 operations
  to degree 325 / 113 operations (package 52): 65.93% lower degree at
  the same arithmetic cost.
* The twelve-positive point improves from degree 118 / 104 operations
  to degree 84 / 103 operations (package 61).
* The thirteen-positive point changes from degree 34 / 93 operations
  to degree 30 / 94 operations: a degree/cost tradeoff (package 61).

The repository's nine-positive and ten-unrestricted-variable points remain
separate. No globally simplest equation or literature-wide priority is
claimed. The new constructions retain the native K215 endpoint; they do
not invoke Jones's universal polynomial or Sun's ten-integer finalizer.
The inspected comparison sources and their hashes are included.

These are ordinary mathematical proofs formalizable in ZFC. They are not
new end-to-end Lean/Rocq certificates or exported derivations in the
repository's object-language ZFC calculus. Finite checks do not establish
consistency, unsolvability, or the unbounded compiler theorem. See the
report's logical-status section and the component independent reviews.

## Exact coefficients

The two families use different complete fixed tuples and must not be
mixed:

| Family | Radix mask beta | Raw bytes for all four native inputs |
|---|---|---:|
| Integer | `2^1064921 - 1` | 532,479 |
| Positive | `2^590069 - 1` | 295,388 |

The files in each `coefficients/` directory are gzip-compressed minimal
unsigned little-endian byte strings. Every byte is supplied. The ports
are beta, K0, MC, and MF; **MF is already shifted**. Recipes, hashes,
binding manifests, source pins, and inherited calibration proofs accompany
the payloads. In particular, the integer builder reconstructs the entire
tuple from the retained literal tile list. These are fixed ordinary
integers, not unknowns or unresolved machine parameters.

## Reproduce offline

Python 3 and its standard library suffice:

```sh
python3 verify.py
python3 verify.py --optimized
```

The root driver authenticates `MANIFEST.json`, checks the comparison
sources, copies the release into an isolated temporary directory, runs
the component checkers and independently authored audits there, and checks
that literal equation artifacts are reproduced without changing the
delivered files. The optimized run confirms that acceptance conditions
do not disappear with Python's `assert` statements disabled.

The finite checks include literal residual substitutions, both complete
integer restoration maps, exact degrees and nonzero leading coefficients,
positive-circuit arithmetic identities and operation counts, all input
liveness, fixed-data integrity, and the integer coefficient reconstruction.
Normal and optimized receipts are in `certificates/`.

To rebuild the PDF with a standard TeX installation:

```sh
python3 build_report.py
```

This command needs `pdflatex` and the packages listed in `report.tex`.
Recompiled PDF metadata can differ; the distributed manifest seals the
delivered PDF bytes, so verify before changing or recompiling files.

## Archive layout

* `report.tex`, `report.pdf`: integrated proofs, equations, comparison,
  limitations, and further research questions.
* `integer/`: all four integer packets, expanded symbolic polynomials,
  full proof, exact coefficient data, retained dependencies, checkers,
  and an independent mathematical/literal audit.
* `positive/`: both literal arithmetic DAGs, complete proof section,
  coefficient data, retained dependencies, checkers, and independent audit.
* `eleven/`: the three-root extension, exact circuit, full proof,
  fixed data, and independent radical, integrality, and literal audits.
* `baseline/`, `BASELINE.json`: byte-identical pinned comparison sources.
* `RESULTS.json`: compact machine-readable metrics and evidence scope.
* `certificates/`: root reproduction receipts and PDF inspection record.
* `MANIFEST.json`: SHA-256 digests and sizes of every other delivered file.
* `LICENSE`, `NOTICE.md`: license and attribution.

This directory is ready for additive intake alongside the existing
numbered research packages. It does not modify their artifacts or the
active formal equation.
