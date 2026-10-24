# Transfer of a strong Pell root into an existing transport gap

This component supplies two fixed integer polynomials, with all unknowns
ranging over the **strictly positive integers**.

| Polynomial | Unknowns | Exact degree | Live binary operations | Residual system |
|---|---:|---:|---:|---|
| `p12_positive_degree84.json` | 12 | 84 | 103 | 3 equations, degrees 42/13/37, 98 operations |
| `p13_positive_degree30.json` | 13 | 30 | 94 | 4 equations, degrees 15/13/13/14, 87 operations |

The comparison pin is ProveIt commit
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4`, including packages 60–67.
The twelve-variable point improves package 61's degree 118 / 104-operation
point in both measures. The thirteen-variable companion reduces degree
34 to 30 at a cost of one additional operation. No improvement in the
overall smallest number of positive variables is claimed.

`section.tex` gives the complete new mathematical proof. The twelve-variable
construction places a signed strong Pell root in the transport gap,
then eliminates it by a quartic norm. A strict radicand inequality excludes
the norm's zero-denominator branch. A polynomial upper approximation makes
the reconstructed gap positive for both root signs. The existing transport
multiplier is enlarged to make the inverse coordinate positive. The
thirteen-variable companion uses the adaptive main modulus `4*q^2*Y`.

The ordinary proof composes these transformations with the explicitly
stated inherited normalized Pell source, native compiler, and K215/ZFC
refutation calibration. It proves existence equivalence, hence the desired
ZFC-provable equivalence of unsolvability and `Con(ZFC)`. It does not prove
ZFC consistent, claim a global minimum, or provide a new complete Lean/Rocq
or object-language ZFC certificate for the emitted circuit.

## Reproduce

Python 3 and its standard library suffice; no network is used:

```sh
python3 verify.py
python3 -O verify.py
```

The verifier checks byte-identical circuit rebuilding, liveness and operation
counts, full sparse polynomial prefix identities, independent cut-ring
identities for the norm, auxiliary equation and sum-of-squares finalizer,
cancellation-resolved exact degrees and nonzero coefficients, and all four
fixed numeral payloads. It authenticates retained upstream sources against
SHA-256 and Git blob identities. It does not search for an inconsistency
witness or use bounded examples as a proof of the existence theorem.

To regenerate the literal circuits deliberately, run `python3 build.py`.
All intermediate registers are abbreviations, not extra unknowns. Counts
charge binary addition, subtraction and multiplication, including scalar
multiplication and fixed powers of nonconstant registers. Fixed integer
leaves and register reuse are free; these counts are not bit complexity.

## Fixed coefficient binding

`coefficients/ACTIVE_BINDING.json` binds both circuits to the complete compact
package-44 tuple. The four gzip files decode to minimal unsigned little-endian
integers. Their total uncompressed size is 295,388 bytes; the supplied gzip
payloads total 9,445 bytes. `beta = 2^590069 - 1`; `MF` already includes the
source high-mask shift. Individual ports must not be exchanged between
coefficient families.

`SOURCE_PINS.json` identifies every retained upstream file. The source-44
coefficient proof and complete original manifest, package 61's report and
thirteen-variable proof, and package 65's adaptive-carrier proof are retained
under `upstream/`. Earlier source links inside these unchanged documents
refer to their own historical snapshots; the active bindings here are the
ones stated above.

## Integration

Include `section.tex` in the integrated article. It requires standard
`amsmath`, `amssymb`, and `amsthm`; its labels use the `rt-` prefix. The
component contains no standalone PDF because it is intended to accompany
the integrated report. Preserve this component's coefficient payloads,
source ledger, notices and licenses when relocating it.

The mathematical reviewers within this research session checked the signed
root, adaptive modulus and inverse-positive-coordinate arguments independently.
That review is internal research assistance, not external peer review.
