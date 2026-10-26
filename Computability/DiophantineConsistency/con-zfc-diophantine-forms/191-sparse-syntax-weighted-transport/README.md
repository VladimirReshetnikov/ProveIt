# Sparse syntax and weighted Pell transport for Con(ZFC)

This package supplies two explicit ordinary Diophantine equations and an
isolated companion construction. Their absence of solutions is provably
equivalent in ZFC to the syntactic consistency statement for the fixed
effective ZFC presentation calibrated in ProveIt.

The principal new ideas are **finite-proof transport through a non-surjective
formula coding** and **a smaller polynomial weight for signed Pell transport**.
The manuscript gives the new unbounded arguments, states their inherited
interfaces, and prints the full equations and fixed coefficient recipe.

## Results

| Construction | Quantifier domain | Variables | Exact degree | Defining size | Collected coefficient height |
|---|---|---:|---:|---:|---:|
| Incoming Pell Growth 210, immediate direct parent | All integers | 210 | 4 | 150 quadratic rows; 5,282 quartic monomials | 2^40 |
| Affine-horizon companion, minimum 2 | All integers | **209** | 4 | 149 quadratic rows; 5,486 quartic monomials | 2^44 |
| **Sparse syntax, principal direct result** | All integers | **208** | **4** | **148 quadratic rows; 5,987 quartic monomials** | **2^44** |
| Incoming centered free chart, compact comparison | Strictly positive integers | 10 | 206 | 90 binary operations | Fixed large tuple |
| Package 178 whole-product center | Strictly positive integers | 10 | 208 | 116 binary operations | Same fixed tuple |
| **Weighted transport, principal compact result** | Strictly positive integers | **10** | **190** | **120 binary operations** | Same fixed tuple |

Different rows optimize different measures of simplicity. The direct result
trades a larger expanded support and height for fewer integer variables.
The compact result lowers degree at an increased arithmetic-operation count.
No global minimum or literature-wide priority is asserted. Earlier ProveIt
families already have fewer variables in other regimes.

The direct equation is literally

    Q208(x0,...,x207) = R0^2 + ... + R147^2 = 0,

with every quadratic residual given in
`direct208/equations/principal208/equation.json` and the paper's first appendix.
The adjacent `expanded_polynomial.json` lists all
collected coefficients of the quartic. It evaluates C222 directly and uses
its existing C222/ZF/ZFC calibration; it does not simulate K215 or use Jones's
universal polynomial.

The ten-variable polynomial is displayed in the paper and in
`positive190/PROOF.md`. Its 120-operation straight-line program is literal
data in `positive190/equation.json`. Its four fixed coefficients are supplied
as integer payloads and by a complete finite reconstruction recipe. They are
not unspecified parameters or mere size bounds. Its native/K215 calibration
is inherited and explicitly identified.

## Read and reproduce

Start with `report/main.pdf`. The paper is editable as `report/main.tex`,
with its included `.tex` fragments. Python 3.10 or later and the standard
library suffice for the executable checks:

```sh
python3 -B verify_all.py
python3 -O -B verify_all.py
```

The programs run offline. They verify exact polynomial identities, all
declared coordinates, source bindings, projection/restoration certificates,
arithmetic graph structure, coefficient payloads, and the degree-190 leading
form. They do not search for solutions. `VERIFICATION_NORMAL.json` and
`VERIFICATION_OPTIMIZED.json` record the release checks.

To rebuild the paper with a standard TeX Live installation:

```sh
cd report
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

`evaluate.py` evaluates either principal equation at an explicitly supplied
integer tuple. Run `python3 evaluate.py --help` for the input format. Modular
evaluation is only an arithmetic diagnostic, not evidence of an integer zero.

## Proof scope

The delivered claim is an ordinary mathematical proof formalizable in ZFC,
composed with the identified inherited logical calibrations. We have not
produced a new object-language ZFC derivation or rebuilt an end-to-end
Lean/Rocq dependency closure. Exact finite checks validate the delivered
algebraic artifacts; the unbounded Pell, finite-proof, and logical arguments
are given in the manuscript and inherited proof sources.

The new proof neither assumes nor establishes Con(ZFC). It proves an
equivalence between two arithmetic statements. The positive-variable domain
of the compact equation is part of its theorem and must be preserved.

## Archive map

| Path | Contents |
|---|---|
| `report/` | PDF, editable LaTeX, exact residual appendix, metric definitions |
| `direct208/` | Sparse compiler, literal quartic, full expansion, source audit, projections and chart certificates |
| `positive190/` | Complete compact polynomial, fixed coefficient payloads/recipe, proof and exact independent verifier |
| `affine209/` | Minimum-2, minimum-8, and minimum-16 affine-horizon companions and certificates |
| `reviews/` | Separately assigned internal mathematical reviews and independent algebra/depth checks |
| `dependencies/` | Unchanged immediate parent archive, with its inherited sources and certificates |
| `verify_all.py` | Offline ordered release verification |
| `evaluate.py` | Literal evaluators for explicitly provided tuples |
| `INTEGRATION.md` | Suggested additive ProveIt integration and comparison wording |
| `MANIFEST.sha256` | SHA-256 bindings for all release files except the manifest itself |

The internal reviews were AI-assisted and are not external human peer review.
The repository snapshot is `d123610bc98fef2006bff1c9466bc3f1221003e7`.
Component source ledgers name and hash their precise inputs. See `NOTICE.md`
for attribution and the inherited proof boundary.
